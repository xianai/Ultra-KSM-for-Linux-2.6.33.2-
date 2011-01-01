/*
 * Memory merging support.
 *
 * This code enables dynamic sharing of identical pages found in different
 * memory areas, even if they are not shared by fork()
 *
 * Copyright (C) 2008-2009 Red Hat, Inc.
 * Authors:
 *	Izik Eidus
 *	Andrea Arcangeli
 *	Chris Wright
 *	Hugh Dickins
 *
 * This work is licensed under the terms of the GNU GPL, version 2.
 */

#include <linux/errno.h>
#include <linux/mm.h>
#include <linux/fs.h>
#include <linux/mman.h>
#include <linux/sched.h>
#include <linux/rwsem.h>
#include <linux/pagemap.h>
#include <linux/rmap.h>
#include <linux/spinlock.h>
#include <linux/jhash.h>
#include <linux/delay.h>
#include <linux/kthread.h>
#include <linux/wait.h>
#include <linux/slab.h>
#include <linux/rbtree.h>
#include <linux/memory.h>
#include <linux/mmu_notifier.h>
#include <linux/swap.h>
#include <linux/ksm.h>
#include <linux/crypto.h>
#include <linux/scatterlist.h>
#include <crypto/hash.h>
#include <linux/random.h>
#include <linux/math64.h>
#include <linux/gcd.h>

#include <asm/tlbflush.h>
#include "internal.h"

#define CONFIG_USE_KSM_MEMCMPX86 1





#ifdef CONFIG_USE_KSM_MEMCMPX86
#undef memcmp
#define memcmp memcmpx86
/*
int memcmpx86b (__const void *__s1, __const void *__s2, size_t __n)
{
   register int __res;
  __asm__ __volatile__
    ("cld\n\t"
     "testl %3,%3\n\t"
     "repe; cmpsb\n\t"
     "je        1f\n\t"
     "sbbl      %0,%0\n\t"
     "orl       $1,%0\n"
     "1:"
     : "=&a" (__res), "+&S" (__s1), "+&D" (__s2), "+&c" (__n)
     : "0" (0)
     : "cc");
  return __res;
}
*/


int memcmpx86 (void *__s1, void *__s2, size_t __n)
{

  //printf("si=%p\n", __s1);
   size_t num = __n / sizeof(int);
   register int __res;
  __asm__ __volatile__
    ("cld\n\t"
     "testl %3,%3\n\t"
     "repe; cmpsd\n\t"
     "je        1f\n\t"
     "sbbl      %0,%0\n\t"
     "orl       $1,%0\n"
     "1:"
     : "=&a" (__res), "+&S" (__s1), "+&D" (__s2), "+&c" (num)
     : "0" (0)
     : "cc");

  //printf("si=%p\n", __s1);
  return __res;
}

#endif









#define get_rmap_addr(x)	((x)->address & PAGE_MASK)



#define UNSTABLE_FLAG	0x1	/* is a node of the unstable tree */
#define STABLE_FLAG	0x2	/* is listed from the stable tree */
//#define FULL_HASH_FLAG  0x4	/* is it fully hashed ?*/

#define IS_ADDR_FLAG	1
#define is_addr(ptr)		((unsigned long)(ptr) & IS_ADDR_FLAG)
#define set_is_addr(ptr)	((ptr) |= IS_ADDR_FLAG)
#define get_clean_addr(ptr)	(((ptr) & ~(__typeof__(ptr))IS_ADDR_FLAG ))




static struct kmem_cache *rmap_item_cache;
static struct kmem_cache *stable_node_cache;
static struct kmem_cache *node_vma_cache;
static struct kmem_cache *vma_slot_cache;
static struct kmem_cache *tree_node_cache;

static unsigned long long ksm_pages_scanned = 0;

static unsigned long long ksm_pages_round_scanned = 0;

static unsigned long long ksm_pages_round_collision = 0;

/* The number of nodes in the stable tree */
static unsigned long ksm_pages_shared;

/* The number of page slots additionally sharing those nodes */
static unsigned long ksm_pages_sharing;

/* The number of nodes in the unstable tree */
static unsigned long ksm_pages_unshared;

/* The number of rmap_items in use: to calculate pages_volatile */
static unsigned long ksm_rmap_items;


static unsigned long ksm_stable_nodes;

/* Number of pages ksmd should scan in one batch, in ratio of millionth */
static unsigned long ksm_scan_batch_pages = 100;

/* Milliseconds ksmd should sleep between batches */
static unsigned int ksm_thread_sleep_jiffies = 2;

static unsigned long stable_tree_sample_num;


#define KSM_SCAN_RATIO_MAX	100

/* minimum scan ratio for a vma, in unit of millionth */
static unsigned int ksm_min_scan_ratio = 5;

/* Inter vma duplication number table page pointer array, initialized at startup */
#define KSM_DUP_VMA_MAX		2048
static unsigned int *ksm_inter_vma_table;

static struct vma_slot **ksm_vma_table;
static unsigned int ksm_vma_table_size = 2048;
static unsigned long ksm_vma_table_num = 0;
static unsigned long ksm_vma_table_index_end = 0;

static unsigned long long ksm_scan_round = 1;

/* How fast the scan ratio is changed */
static unsigned int ksm_scan_ratio_delta = 5;

/* Each rung of this ladder is a list of VMAs having a same scan ratio */
static struct scan_rung *ksm_scan_ladder;
static unsigned int ksm_scan_ladder_size;

static unsigned long ksm_vma_slot_num = 0;

static u64 ksm_sleep_times = 0;

#define KSM_RUN_STOP	0
#define KSM_RUN_MERGE	1
static unsigned int ksm_run = KSM_RUN_STOP;

static DECLARE_WAIT_QUEUE_HEAD(ksm_thread_wait);
static DEFINE_MUTEX(ksm_thread_mutex);


struct list_head vma_slot_new = LIST_HEAD_INIT(vma_slot_new);
struct list_head vma_slot_noadd = LIST_HEAD_INIT(vma_slot_noadd);
struct list_head vma_slot_del = LIST_HEAD_INIT(vma_slot_del);
static DEFINE_SPINLOCK(vma_slot_list_lock);

/* The stable and unstable tree heads */
static struct rb_root root_unstable_tree = RB_ROOT;
static struct list_head stable_node_list = LIST_HEAD_INIT(stable_node_list);/* all stable nodes */

/* This is a list for stable nodes that can cause two level hash collision,
 * but with different page content, this should be really rare.
 * But if it really happens, this is the place they should go.
 */
//static struct list_head stable_node_hell = LIST_HEAD_INIT(stable_node_hell);
static struct list_head unstable_tree_node_list = LIST_HEAD_INIT(unstable_tree_node_list);


/* We use two groups of structs to speed up the rehashing of stable tree */
static struct list_head
stable_tree_node_list[2] = {LIST_HEAD_INIT(stable_tree_node_list[0]),
			    LIST_HEAD_INIT(stable_tree_node_list[1])};

static struct list_head *stable_tree_node_listp = &stable_tree_node_list[0];
static struct rb_root root_stable_tree[2] = {RB_ROOT, RB_ROOT};
static struct rb_root *root_stable_treep = &root_stable_tree[0];
unsigned long stable_tree_index = 0;



/* In mseconds */
unsigned long slots_enter_interval = 10;

/* The jiffiy when last ksm_enter_all_slots was run */
unsigned long slots_enter_last = 0;

struct vma_slot {
	struct list_head ksm_list;
	struct list_head slot_list;
	unsigned long dedup_ratio;
	int ksm_index; /* -1 if vma is not in inter-table,
				positive otherwise */
	unsigned long pages_scanned;
	unsigned long last_scanned;
	unsigned char need_sort;
	unsigned char need_rerand;
	unsigned long pages_to_scan;
	struct scan_rung *rung;
	struct page **rmap_list_pool;
	unsigned long *pool_counts;
	unsigned long pool_size;
	struct vm_area_struct *vma;
	struct mm_struct *mm;
	unsigned long ctime_j;
	unsigned long pages;
	unsigned long slot_scanned; /* It's scanned in this round */
	unsigned long fully_scanned;
};


#define KSM_KMEM_CACHE(__struct, __flags) kmem_cache_create("ksm_"#__struct,\
		sizeof(struct __struct), __alignof__(struct __struct),\
		(__flags), NULL)


#define __round_mask(x,y) ((__typeof__(x))((y)-1))
#define round_up(x,y) ((((x)-1) | __round_mask(x,y))+1)
#define round_down(x,y) ((x) & ~__round_mask(x,y))

static inline unsigned long vma_pool_size(struct vm_area_struct *vma)
{
	return (round_up(sizeof(struct rmap_list_entry) * vma_pages(vma),
			PAGE_SIZE) >> PAGE_SHIFT);
}

//-----------------------------------------------------------------------------
static inline unsigned int intertab_vma_offset(int i, int j)
{
	int swap;
	if (i < j) {
		//printf(KERN_ERR "Inter vma table index error\n");
		//BUG();
		swap = i;
		i = j;
		j = swap;
	}

	return i * (i+1) / 2 + j;
}

//-----------------------------------------------------------------------------

static int __init ksm_slab_init(void)
{
	rmap_item_cache = KSM_KMEM_CACHE(rmap_item, 0);
	if (!rmap_item_cache)
		goto out;

	stable_node_cache = KSM_KMEM_CACHE(stable_node, 0);
	if (!stable_node_cache)
		goto out_free1;

	node_vma_cache = KSM_KMEM_CACHE(node_vma, 0);
	if (!node_vma_cache)
		goto out_free2;

	vma_slot_cache = KSM_KMEM_CACHE(vma_slot, 0);
	if (!vma_slot_cache)
		goto out_free3;

	tree_node_cache = KSM_KMEM_CACHE(tree_node, 0);
	if (!tree_node_cache)
		goto out_free4;

	return 0;

out_free4:
	kmem_cache_destroy(vma_slot_cache);
out_free3:
	kmem_cache_destroy(node_vma_cache);
out_free2:
	kmem_cache_destroy(stable_node_cache);
out_free1:
	kmem_cache_destroy(rmap_item_cache);
out:
	return -ENOMEM;
}

static void __init ksm_slab_free(void)
{
	kmem_cache_destroy(stable_node_cache);
	kmem_cache_destroy(rmap_item_cache);
	kmem_cache_destroy(node_vma_cache);
	kmem_cache_destroy(vma_slot_cache);
	kmem_cache_destroy(tree_node_cache);
}

static inline struct node_vma *alloc_node_vma(void)
{
	struct node_vma *node_vma;
	node_vma = kmem_cache_zalloc(node_vma_cache, GFP_KERNEL);
	if (node_vma) {
		INIT_HLIST_HEAD(&node_vma->rmap_hlist);
		INIT_HLIST_NODE(&node_vma->hlist);
		node_vma->last_update = 0;
	}
	return node_vma;
}

static inline void free_node_vma(struct node_vma *node_vma)
{
	kmem_cache_free(node_vma_cache, node_vma);
}


static inline struct vma_slot *alloc_vma_slot(void)
{
	struct vma_slot *slot;
	slot = kmem_cache_zalloc(vma_slot_cache, GFP_KERNEL);
	if (slot) {
		INIT_LIST_HEAD(&slot->ksm_list);
		INIT_LIST_HEAD(&slot->slot_list);
		slot->ksm_index = -1;
		slot->need_rerand = 1;
	}
	return slot;
}

static inline void free_vma_slot(struct vma_slot *vma_slot)
{
	kmem_cache_free(vma_slot_cache, vma_slot);
}



static inline struct rmap_item *alloc_rmap_item(void)
{
	struct rmap_item *rmap_item;

	rmap_item = kmem_cache_zalloc(rmap_item_cache, GFP_KERNEL);
	if (rmap_item) {
		/* bug on lowest bit is not clear for flag use */
		BUG_ON(is_addr(rmap_item));
		ksm_rmap_items++;
		//INIT_LIST_HEAD(&rmap_item->collision);
	}
	return rmap_item;
}

static inline void free_rmap_item(struct rmap_item *rmap_item)
{
	ksm_rmap_items--;
	rmap_item->slot = NULL;	/* debug safety */
	kmem_cache_free(rmap_item_cache, rmap_item);
}

static inline struct stable_node *alloc_stable_node(void)
{
	struct stable_node *node;
	node = kmem_cache_alloc(stable_node_cache, GFP_KERNEL | GFP_ATOMIC);
	if (!node)
		return NULL;

	INIT_HLIST_HEAD(&node->hlist);
	list_add(&node->all_list, &stable_node_list);
	ksm_stable_nodes++;
	return node;
}

static inline void free_stable_node(struct stable_node *stable_node)
{
	ksm_stable_nodes--;
	list_del(&stable_node->all_list);
	kmem_cache_free(stable_node_cache, stable_node);
}

static inline struct tree_node *alloc_tree_node(struct list_head *list)
{
	struct tree_node *node;
	node = kmem_cache_zalloc(tree_node_cache, GFP_KERNEL | GFP_ATOMIC);
	if (!node)
		return NULL;

	node->sub_root = RB_ROOT;
	list_add(&node->all_list, list);
	return node;
}

static inline void free_tree_node(struct tree_node *node)
{
	list_del(&node->all_list);
	kmem_cache_free(tree_node_cache, node);
}


/*
int ksm_fork(struct mm_struct *mm, struct mm_struct *oldmm)
*/

static inline int in_stable_tree(struct rmap_item *rmap_item)
{
	return rmap_item->address & STABLE_FLAG;
}

static void hold_anon_vma(struct rmap_item *rmap_item,
			  struct anon_vma *anon_vma)
{
	rmap_item->anon_vma = anon_vma;
	atomic_inc(&anon_vma->ksm_refcount);
}

static void drop_anon_vma(struct rmap_item *rmap_item)
{
	struct anon_vma *anon_vma = rmap_item->anon_vma;

	if (atomic_dec_and_lock(&anon_vma->ksm_refcount, &anon_vma->lock)) {
		int empty = list_empty(&anon_vma->head);
		spin_unlock(&anon_vma->lock);
		if (empty)
			anon_vma_free(anon_vma);
	}
}

/*
 * ksmd, and unmerge_and_remove_all_rmap_items(), must not touch an mm's
 * page tables after it has passed through ksm_exit() - which, if necessary,
 * takes mmap_sem briefly to serialize against them.  ksm_exit() does not set
 * a special flag: they can just back out as soon as mm_users goes to zero.
 * ksm_test_exit() is used throughout to make this test for exit: in some
 * places for correctness, in some places just to avoid unnecessary work.
 */
static inline bool ksm_test_exit(struct mm_struct *mm)
{
	return atomic_read(&mm->mm_users) == 0;
}

/*
 * We use break_ksm to break COW on a ksm page: it's a stripped down
 *
 *	if (get_user_pages(current, mm, addr, 1, 1, 1, &page, NULL) == 1)
 *		put_page(page);
 *
 * but taking great care only to touch a ksm page, in a VM_MERGEABLE vma,
 * in case the application has unmapped and remapped mm,addr meanwhile.
 * Could a ksm page appear anywhere else?  Actually yes, in a VM_PFNMAP
 * mmap of /dev/mem or /dev/kmem, where we would not want to touch it.
 */
static int break_ksm(struct vm_area_struct *vma, unsigned long addr)
{
	struct page *page;
	int ret = 0;

	do {
		cond_resched();
		page = follow_page(vma, addr, FOLL_GET);
		if (!page)
			break;
		if (PageKsm(page)) {
			ret = handle_mm_fault(vma->vm_mm, vma, addr,
							FAULT_FLAG_WRITE);
			if (!(ret & (VM_FAULT_WRITE | VM_FAULT_SIGBUS | VM_FAULT_OOM)))
				printk(KERN_ERR "KSM: !!!!!!!!ret=%d\n", ret);
		} else
			ret = VM_FAULT_WRITE;
		put_page(page);
	} while (!(ret & (VM_FAULT_WRITE | VM_FAULT_SIGBUS | VM_FAULT_OOM)));
	/*
	 * We must loop because handle_mm_fault() may back out if there's
	 * any difficulty e.g. if pte accessed bit gets updated concurrently.
	 *
	 * VM_FAULT_WRITE is what we have been hoping for: it indicates that
	 * COW has been broken, even if the vma does not permit VM_WRITE;
	 * but note that a concurrent fault might break PageKsm for us.
	 *
	 * VM_FAULT_SIGBUS could occur if we race with truncation of the
	 * backing file, which also invalidates anonymous pages: that's
	 * okay, that truncation will have unmapped the PageKsm for us.
	 *
	 * VM_FAULT_OOM: at the time of writing (late July 2009), setting
	 * aside mem_cgroup limits, VM_FAULT_OOM would only be set if the
	 * current task has TIF_MEMDIE set, and will be OOM killed on return
	 * to user; and ksmd, having no mm, would never be chosen for that.
	 *
	 * But if the mm is in a limited mem_cgroup, then the fault may fail
	 * with VM_FAULT_OOM even if the current task is not TIF_MEMDIE; and
	 * even ksmd can fail in this way - though it's usually breaking ksm
	 * just to undo a merge it made a moment before, so unlikely to oom.
	 *
	 * That's a pity: we might therefore have more kernel pages allocated
	 * than we're counting as nodes in the stable tree; but ksm_do_scan
	 * will retry to break_cow on each pass, so should recover the page
	 * in due course.  The important thing is to not let VM_MERGEABLE
	 * be cleared while any such pages might remain in the area.
	 */
	return (ret & VM_FAULT_OOM) ? -ENOMEM : 0;
}

static void break_cow(struct rmap_item *rmap_item)
{
	struct vm_area_struct *vma = rmap_item->slot->vma;
	struct mm_struct *mm = vma->vm_mm;
	unsigned long addr = get_rmap_addr(rmap_item);

	/*
	 * It is not an accident that whenever we want to break COW
	 * to undo, we also need to drop a reference to the anon_vma.
	 */
	//drop_anon_vma(rmap_item);

	if (ksm_test_exit(mm))
		goto out;

	break_ksm(vma, addr);
out:
	return;
}

/* can be refactored & beautified */
static void ksm_intertab_clear(struct vma_slot *slot)
{
	int i;
	unsigned index;

	for (i = 0; i <= slot->ksm_index; i++) {
		index = intertab_vma_offset(slot->ksm_index, i);
		ksm_inter_vma_table[index] = 0; /* Cleared data for this round */
	}

	for (i = slot->ksm_index + 1; i < ksm_vma_table_index_end; i++) {
		index = intertab_vma_offset(slot->ksm_index, i);
		ksm_inter_vma_table[index] = 0;
	}

}

/*
 * Returns the next collision node that has replaced this node,
 * returns NULL if it has no collision.
 */
static void remove_node_from_stable_tree(struct stable_node *stable_node,
					 int remove_tree_node)
{
	struct node_vma *node_vma;
	struct rmap_item *rmap_item;
	struct hlist_node *hlist, *rmap_hlist, *n;

	if (!hlist_empty(&stable_node->hlist)) {
		hlist_for_each_entry_safe(node_vma, hlist, n,
					  &stable_node->hlist, hlist) {
			hlist_for_each_entry(rmap_item, rmap_hlist,
					     &node_vma->rmap_hlist, hlist) {
				ksm_pages_sharing--;

				drop_anon_vma(rmap_item);
				rmap_item->address &= PAGE_MASK;
			}
			free_node_vma(node_vma);
			cond_resched();
		}

		/* the last one is counted as shared */
		ksm_pages_shared--;
		ksm_pages_sharing++;
	}

/*
	hlist_for_each_entry(rmap_item, hlist, &stable_node->hlist, hlist) {
		if (rmap_item->hlist.next)
			ksm_pages_sharing--;
		else
			ksm_pages_shared--;
		drop_anon_vma(rmap_item);
		rmap_item->address &= PAGE_MASK;
		cond_resched();
	}
*/
/*
	if (stable_node_is_rbnode(stable_node)) {
		if (list_empty(&stable_node->collision))
			rb_erase(&stable_node->node, &root_stable_tree);
		else {
			newnode = list_entry(stable_node->collision.next,
					     struct stable_node, collision);
			rb_replace_node(&stable_node->node, &newnode->node,
					&root_stable_tree);
			BUG_ON(newnode->checksum_val !=
			       stable_node->checksum_val);
			list_del_init(&stable_node->collision);
		}
		stable_node->node.rb_parent_color = 0;
	} else if (!list_empty(&stable_node->collision)) {
		list_del_init(&stable_node->collision);
	}
*/
/*
	status = stable_node->status;
	switch (status) {
	case STAT_COL:
		list_del(&stable_node->collision);
		break;

	case STAT_RB:

		if (list_empty(&stable_node->collision))
			rb_erase(&stable_node->node, &root_stable_tree);
		else {
			newnode = list_entry(stable_node->collision.next,
					     struct stable_node, collision);
			rb_replace_node(&stable_node->node, &newnode->node,
					&root_stable_tree);
			newnode->status = STAT_RB;
			BUG_ON(newnode->checksum_val !=
			       stable_node->checksum_val);
			list_del(&stable_node->collision);
		}

		break;

	case STAT_NONE:
		break;

	default:
		BUG();
	}
*/
	if (stable_node->tree_node) {
		rb_erase(&stable_node->node, &stable_node->tree_node->sub_root);
		if (RB_EMPTY_ROOT(&stable_node->tree_node->sub_root) &&
		    remove_tree_node) {
			rb_erase(&stable_node->tree_node->node, root_stable_treep);
			free_tree_node(stable_node->tree_node);
		} else
			stable_node->tree_node->count--;
	} else
		list_del(&stable_node->hell_node);

	free_stable_node(stable_node);
}


/*
 * get_ksm_page: checks if the page indicated by the stable node
 * is still its ksm page, despite having held no reference to it.
 * In which case we can trust the content of the page, and it
 * returns the gotten page; but if the page has now been zapped,
 * remove the stale node from the stable tree and return NULL.
 *
 * You would expect the stable_node to hold a reference to the ksm page.
 * But if it increments the page's count, swapping out has to wait for
 * ksmd to come around again before it can free the page, which may take
 * seconds or even minutes: much too unresponsive.  So instead we use a
 * "keyhole reference": access to the ksm page from the stable node peeps
 * out through its keyhole to see if that page still holds the right key,
 * pointing back to this stable node.  This relies on freeing a PageAnon
 * page to reset its page->mapping to NULL, and relies on no other use of
 * a page to put something that might look like our key in page->mapping.
 *
 * include/linux/pagemap.h page_cache_get_speculative() is a good reference,
 * but this is different - made simpler by ksm_thread_mutex being held, but
 * interesting for assuming that no other use of the struct page could ever
 * put our expected_mapping into page->mapping (or a field of the union which
 * coincides with page->mapping).  The RCU calls are not for KSM at all, but
 * to keep the page_count protocol described with page_cache_get_speculative.
 *
 * Note: it is possible that get_ksm_page() will return NULL one moment,
 * then page the next, if the page is in between page_freeze_refs() and
 * page_unfreeze_refs(): this shouldn't be a problem anywhere, the page
 * is on its way to being freed; but it is an anomaly to bear in mind.
 */
static struct page *get_ksm_page(struct stable_node *stable_node,
				 int remove_tree_node)
{
	struct page *page;
	void *expected_mapping;

	page = pfn_to_page(stable_node->kpfn);
	expected_mapping = (void *)stable_node +
				(PAGE_MAPPING_ANON | PAGE_MAPPING_KSM);
	rcu_read_lock();
	if (page->mapping != expected_mapping)
		goto stale;
	if (!get_page_unless_zero(page))
		goto stale;
	if (page->mapping != expected_mapping) {
		put_page(page);
		goto stale;
	}
	rcu_read_unlock();
	return page;
stale:
	rcu_read_unlock();
	remove_node_from_stable_tree(stable_node, remove_tree_node);

	return NULL;
}

/*
 * Removing rmap_item from stable or unstable tree.
 * This function will clean the information from the stable/unstable tree.
 * return the next hash collision rmap_item if possible, otherwise NULL
 */
static
struct rmap_item *remove_rmap_item_from_tree(struct rmap_item *rmap_item)
{
	struct rmap_item *next_item = NULL;

	if (rmap_item->address & STABLE_FLAG) {
		struct stable_node *stable_node;
		struct node_vma *node_vma;
		struct page *page;

		node_vma = rmap_item->head;
		stable_node = node_vma->head;
		page = get_ksm_page(stable_node, 1);
		if (!page)
			goto out;

		//lock_page(page);
		hlist_del(&rmap_item->hlist);
		//unlock_page(page);
		put_page(page);

		if (hlist_empty(&node_vma->rmap_hlist)) {
			hlist_del(&node_vma->hlist);
			free_node_vma(node_vma);
		}

		if (hlist_empty(&stable_node->hlist)) {
			/* do NOT call remove_node_from_stable_tree() here,
			 * it's possible for a forked rmap_item not in
			 * stable tree while the in-tree rmap_items were
			 * deleted.
			 */
			ksm_pages_shared--;
		} else
			ksm_pages_sharing--;


		drop_anon_vma(rmap_item);
	} else if (rmap_item->address & UNSTABLE_FLAG) {
		//unsigned char age;

		/*
		 * Usually ksmd can and must skip the rb_erase, because
		 * root_unstable_tree was already reset to RB_ROOT.
		 * But be careful when an mm is exiting: do the rb_erase
		 * if this rmap_item was inserted by this scan, rather
		 * than left over from before.
		 */
//		age = (unsigned char)(ksm_scan.seqnr - rmap_item->address);
//		BUG_ON(age > 1);
//		if (!age)
		if (rmap_item->append_round == ksm_scan_round) {
			rb_erase(&rmap_item->node, &rmap_item->tree_node->sub_root);
			if (RB_EMPTY_ROOT(&rmap_item->tree_node->sub_root)) {
				rb_erase(&rmap_item->tree_node->node, &root_unstable_tree);
				free_tree_node(rmap_item->tree_node);
			} else
				rmap_item->tree_node->count--;
		}
		ksm_pages_unshared--;
	}

	rmap_item->address &= PAGE_MASK;
	rmap_item->checksum_full = 0;

out:
	cond_resched();		/* we're called from many long loops */
	return next_item;
}


/* It must be done AFTER vma is unlinked from its mm */
void ksm_del_vma_slot(struct vma_slot *slot)
{
	int i, j;
	struct rmap_list_entry *entry;

	/* mutex lock contention maybe intensive, other idea ? */
	BUG_ON(list_empty(&slot->ksm_list) || !slot->rung);

	if (slot->rung->current_scan == &slot->ksm_list)
		slot->rung->current_scan = slot->rung->current_scan->next;

	list_del_init(&slot->ksm_list);
	slot->rung->vma_num--;
	if (slot->fully_scanned)
		slot->rung->fully_scanned_slots--;

	if (slot->rung->current_scan == &slot->rung->vma_list) {
		/* This rung finishes a round */
		slot->rung->round_finished = 1;
		slot->rung->current_scan = slot->rung->vma_list.next;
		BUG_ON(slot->rung->current_scan == &slot->rung->vma_list && !list_empty(&slot->rung->vma_list));
	}

	for (i = 0; i < ksm_vma_table_index_end; i++) {
		if ((slot == ksm_vma_table[i])) {
			//cal_dedup_ratio_clear(vma);
			ksm_intertab_clear(slot);
			ksm_vma_table_num--;
			ksm_vma_table[i] = NULL;
			if (i == ksm_vma_table_index_end - 1)
				ksm_vma_table_index_end--;
			break;
		}
	}

	/* vma may be already deleted */
	//BUG_ON(slot->pool_size != vma_pool_size(vma));

	if (!slot->rmap_list_pool)
		goto out;

	for (i = 0; i < slot->pool_size; i++) {
		void *addr;

		if (!slot->rmap_list_pool[i])
			continue;

		addr = kmap(slot->rmap_list_pool[i]);
		BUG_ON(!addr);
		for (j = 0; j < PAGE_SIZE / sizeof(*entry); j++) {
			entry = (struct rmap_list_entry *)addr + j;
			if (is_addr(entry->addr))
				continue;
			if (!entry->item)
				continue;

			remove_rmap_item_from_tree(entry->item);
			free_rmap_item(entry->item);
			slot->pool_counts[i]--;
		}
		BUG_ON(slot->pool_counts[i]);
		kunmap(slot->rmap_list_pool[i]);
		__free_page(slot->rmap_list_pool[i]);
	}
	kfree(slot->rmap_list_pool);
	kfree(slot->pool_counts);
out:
	slot->rung = NULL;
	//printk(KERN_ERR "KSM: del slot for vma=%x\n", (unsigned int)vma);
	free_vma_slot(slot);
	BUG_ON(!ksm_vma_slot_num);
	ksm_vma_slot_num--;
}


static void inline cleanup_vma_slots(void)
{
	struct vma_slot *slot;

	spin_lock(&vma_slot_list_lock);
	while (!list_empty(&vma_slot_del)) {
		slot = list_entry(vma_slot_del.next, struct vma_slot, slot_list);
		list_del(&slot->slot_list);
		spin_unlock(&vma_slot_list_lock);
		ksm_del_vma_slot(slot);
		spin_lock(&vma_slot_list_lock);
	}
	spin_unlock(&vma_slot_list_lock);
}

struct rwsem_waiter {
	struct list_head list;
	struct task_struct *task;
	unsigned int flags;
#define RWSEM_WAITING_FOR_READ	0x00000001
#define RWSEM_WAITING_FOR_WRITE	0x00000002
};

/**
 * Need to do two things:
 * 1. check if slot was moved to del list
 * 2. make sure the mmap_sem is manipulated under valid vma.
 *
 * My concern here is that in some cases, this may make
 * vma_slot_list_lock() waiters to serialized further by some
 * sem->wait_lock, can this really be expensive?
 *
 * @param slot
 *
 * @return
 * 0: if successfully locked mmap_sem
 * -ENOENT: this slot was moved to del list
 * -EBUSY: vma lock failed
 */
static int down_read_slot_mmap_sem(struct vma_slot *slot)
{
	struct vm_area_struct *vma;
	struct mm_struct *mm;
	struct rw_semaphore *sem;

	spin_lock(&vma_slot_list_lock);

	/* the slot_list was removed and inited from new list, when it enters
	 * ksm_list. If now it's not empty, then it must be moved to del list
	 */
	if (!list_empty(&slot->slot_list)) {
		spin_unlock(&vma_slot_list_lock);
		return -ENOENT;
	}

	BUG_ON(slot->pages != vma_pages(slot->vma));
	/* Ok, vma still valid */
	vma = slot->vma;
	mm = vma->vm_mm;
	sem = &mm->mmap_sem;
	if (down_read_trylock(sem)) {
		spin_unlock(&vma_slot_list_lock);
		return 0;
	}

	spin_unlock(&vma_slot_list_lock);
	return -EBUSY;
}

static inline unsigned long
vma_page_address(struct page *page, struct vm_area_struct *vma)
{
	pgoff_t pgoff = page->index << (PAGE_CACHE_SHIFT - PAGE_SHIFT);
	unsigned long address;

	address = vma->vm_start + ((pgoff - vma->vm_pgoff) << PAGE_SHIFT);
	if (unlikely(address < vma->vm_start || address >= vma->vm_end)) {
		/* page should be within @vma mapping range */
		return -EFAULT;
	}
	return address;
}


/* return 0 on success with item's mmap_sem locked */
static int get_mergeable_page_lock_mmap(struct rmap_item *item)
{
	struct mm_struct *mm;
	//unsigned long addr = item->address;
	struct vm_area_struct *vma;
	//struct page *page;
	struct vma_slot *slot = item->slot;
	int err = -EINVAL;

	struct page *page;

	BUG_ON(!item->slot);
	/**
	 * down_read_slot_mmap_sem() returns non-zero if the slot has
	 * been removed by ksm_remove_vma().
	 */
	if (down_read_slot_mmap_sem(slot))
		return -EBUSY;

	mm = slot->vma->vm_mm;
	vma = slot->vma;

	if (ksm_test_exit(mm)) {
		//err = -EINVAL;
		goto failout_up;
	}

	page = item->page;
	rcu_read_lock();
	if (!get_page_unless_zero(page)) {
		rcu_read_unlock();
		goto failout_up;
	}
	if (item->slot->vma->anon_vma != page_anon_vma(page) ||
	    vma_page_address(page, item->slot->vma) != get_rmap_addr(item)) {
		put_page(page);
		rcu_read_unlock();
		goto failout_up;
	}
	rcu_read_unlock();
	//*pagep = page;
	return 0;

/*
	page = follow_page(vma, addr, FOLL_GET);
	if (!page)
		goto failout;
	if (PageAnon(page)) {
		flush_anon_page(vma, page, addr);
		flush_dcache_page(page);
	} else {
		put_page(page);
		goto failout;
	}
	return page;
*/

failout_up:
	up_read(&mm->mmap_sem);
	return err;
}

/*
 * return the page if it's get from tree_rmap_item,
 * return NULL, if page cannot be get from tree_rmap_item and if colli_item not NULL,
 * this rb_tree node has been replaced by the colli_item.     									    ,
 */
static int get_tree_rmap_item_page(struct rmap_item *tree_rmap_item)
{
	int err;

	err = get_mergeable_page_lock_mmap(tree_rmap_item);

	if (err == -EINVAL) {
		/* its page map has been changed, remove it */
		remove_rmap_item_from_tree(tree_rmap_item);
	}

	/* The page is gotten and mmap_sem is locked now. */
	return err;
}



static inline int ksm_vma_flags_ok(struct vm_area_struct *vma)
{
	return !(vma->vm_flags & (VM_PFNMAP | VM_IO  | VM_DONTEXPAND |
				 VM_RESERVED  | VM_HUGETLB | VM_INSERTPAGE |
				 VM_NONLINEAR | VM_MIXEDMAP | VM_SAO |
				 VM_SHARED  | VM_MAYSHARE ) );
}

static inline int vma_can_enter(struct vm_area_struct *vma)
{
	return ksm_vma_flags_ok(vma);
}

/* must be done before linked to mm */
inline void ksm_vma_add_new(struct vm_area_struct *vma)
{
	struct vma_slot *slot;

/*
	if (!strcmp("best_case", vma->vm_mm->owner->comm)) {
		printk(KERN_ERR "KSM: add new task=%s vma=%p pages=%lu\n", vma->vm_mm->owner->comm, vma, vma_pages(vma));
	}
*/

	if (!vma_can_enter(vma)) {
		vma->ksm_vma_slot = NULL;
		return;
	}

	slot = alloc_vma_slot();
	if (!slot)
		return;

	//BUG_ON(vma->ksm_vma_slot);

	vma->ksm_vma_slot = slot;
	slot->vma = vma;
	slot->mm = vma->vm_mm;
	slot->ctime_j = jiffies;
	slot->pages = vma_pages(vma);
	spin_lock(&vma_slot_list_lock);
	list_add_tail(&slot->slot_list, &vma_slot_new);
	spin_unlock(&vma_slot_list_lock);

/*
	INIT_LIST_HEAD(&vma->ksm_list);
	vma->dedup_ratio = 0;
	vma->ksm_index = -1;
	vma->pages_scanned = 0;
	vma->pages_to_scan = 0;
	vma->last_scanned = 0;
	vma->need_sort = 0;
	vma->need_rerand = 1;
	vma->rung = 0;
	vma->rmap_list_pool = NULL;
	vma->pool_counts = NULL;
	vma->pool_size = 0;
	//vma->rmap_list = NULL;
	//vma->rmap_num = 0;
	vma->vm_flags &= ~VM_MERGEABLE;
*/
}

/* It must be done AFTER vma is unlinked from its mm */
void ksm_remove_vma(struct vm_area_struct *vma)
{
	struct vma_slot *slot;

	if (!vma->ksm_vma_slot)
		return;

	slot = vma->ksm_vma_slot;
	spin_lock(&vma_slot_list_lock);
	if (list_empty(&slot->slot_list)) {
		/**
		 * This slot has been added, so move to the del list
		 */
		list_add_tail(&slot->slot_list, &vma_slot_del);
	} else {
		/**
		 * It's still on new list. It's ok to free slot directly.
		 */
		list_del(&slot->slot_list);
		free_vma_slot(slot);
	}
	spin_unlock(&vma_slot_list_lock);
	vma->ksm_vma_slot = NULL;
/*
	if (!strcmp("best_case", vma->vm_mm->owner->comm))
		printk(KERN_ERR "KSM: removed task=%s vma=%p\n", vma->vm_mm->owner->comm, vma);
*/
}

/*
 * Though it's very tempting to unmerge in_stable_tree(rmap_item)s rather
 * than check every pte of a given vma, the locking doesn't quite work for
 * that - an rmap_item is assigned to the stable tree after inserting ksm
 * page and upping mmap_sem.  Nor does it fit with the way we skip dup'ing
 * rmap_items from parent to child at fork time (so as not to waste time
 * if exit comes before the next scan reaches it).
 *
 * Similarly, although we'd like to remove rmap_items (so updating counts
 * and freeing memory) when unmerging an area, it's easier to leave that
 * to the next pass of ksmd - consider, for example, how ksmd might be
 * in cmp_and_merge_page on one of the rmap_items we would be removing.
 */
/*
static int unmerge_ksm_pages(struct vm_area_struct *vma,
			     unsigned long start, unsigned long end)
{
	unsigned long addr;
	int err = 0;

	for (addr = start; addr < end && !err; addr += PAGE_SIZE) {
		if (ksm_test_exit(vma->vm_mm))
			break;
		if (signal_pending(current))
			err = -ERESTARTSYS;
		else
			err = break_ksm(vma, addr);
	}
	return err;
}
*/

#if !defined (get16bits)
	#define get16bits(d) ((((uint32_t)(((const uint8_t *)(d))[1])) << 8)\
                       +(uint32_t)(((const uint8_t *)(d))[0]) )
#endif


#define HASH_STRENGTH_FULL		(PAGE_SIZE / sizeof(u32))
#define HASH_STRENGTH_MAX		(HASH_STRENGTH_FULL + 10)

static u32 *random_nums;

/* the number of unsigned long to be taken */
static unsigned long current_sample_num = HASH_STRENGTH_FULL >> 4;
static unsigned long sample_num_delta = 0;
#define SAMPLE_NUM_DELTA_MAX	5
static u64 rshash_pos = 0;
static u64 rshash_neg = 0;
static unsigned long  rshash_neg_cont_zero = 0;
static unsigned long rshash_cost = 0;
static unsigned long memcmp_cost = 0;
static unsigned long calsum_count = 0;

typedef enum {
		RSHASH_STILL,
		RSHASH_TRYUP,
		RSHASH_TRYDOWN,
		RSHASH_NEW,
		RSHASH_PRE_STILL,
} rshash_state_t;

typedef enum {
	GO_UP,
	GO_DOWN,
	OBSCURE,
	STILL,
} rshash_direct_t;


static struct {
	rshash_state_t state;
	rshash_direct_t pre_direct;
	u8 below_count;
	/* Keep a lookup window of size 5, iff above_count/below_count > 3
	 * in this window we stop trying.
	 */
	u8 lookup_window_index;
	u64 stable_benefit;
	unsigned long turn_point_down;
	unsigned long turn_benefit_down;
	unsigned long turn_point_up;
	unsigned long turn_benefit_up;
	unsigned long stable_point;
} rshash_state;

/*   32/3 < they < 32/2 */
#define shiftl	8
#define shiftr	12


#define HASH_FROM_TO(from, to) 				\
for (index = from; index < to; index++) {		\
	pos = random_nums[index];			\
	hash += key[pos];				\
	hash += (hash << shiftl);			\
	hash ^= (hash >> shiftr);			\
}


#define HASH_FROM_DOWN_TO(from, to) 			\
for (index = from - 1; index >= to; index--) {		\
	hash ^= (hash >> shiftr);			\
	hash ^= (hash >> (shiftr*2));			\
	hash -= (hash << shiftl);			\
	hash += (hash << (shiftl*2));			\
	pos = random_nums[index];			\
	hash -= key[pos];				\
}


static u32 random_sample_hash(void *addr, u32 sample_num)
{
	u32 hash = 0xdeadbeef;
	int index, pos, loop = sample_num;
	u32 *key = (u32*)addr;

	if (loop > HASH_STRENGTH_FULL)
		loop = HASH_STRENGTH_FULL;

	HASH_FROM_TO(0, loop);

	if (sample_num > HASH_STRENGTH_FULL) {
		loop = sample_num - HASH_STRENGTH_FULL;
		HASH_FROM_TO(0, loop);
	}

	return hash;
}

static u32 delta_hash(void *addr, int from, int to, u32 hash)
{
	u32 *key = (u32*)addr;
	int index, pos, loop; /* make sure they are int type */

	if (to > from) {
		if (from >= HASH_STRENGTH_FULL) {
			from -= HASH_STRENGTH_FULL;
			to -= HASH_STRENGTH_FULL;
			HASH_FROM_TO(from, to);
		} else if (to <= HASH_STRENGTH_FULL) {
			HASH_FROM_TO(from, to);
		} else {
			HASH_FROM_TO(from, HASH_STRENGTH_FULL);
			HASH_FROM_TO(0, to - HASH_STRENGTH_FULL);
		}
	} else {
		if (from <= HASH_STRENGTH_FULL) {
			HASH_FROM_DOWN_TO(from, to);
		} else if (to >= HASH_STRENGTH_FULL) {
			from -= HASH_STRENGTH_FULL;
			to -= HASH_STRENGTH_FULL;
			HASH_FROM_DOWN_TO(from, to);
		} else {
			HASH_FROM_DOWN_TO(from - HASH_STRENGTH_FULL, 0);
			HASH_FROM_DOWN_TO(HASH_STRENGTH_FULL, to);
		}
	}

	return hash;
}


static inline u32 calc_checksum(struct page *page, int cost_accounting)
{
	u32 val;
	unsigned long tmp;

	void *addr = kmap_atomic(page, KM_USER0);

	val = random_sample_hash(addr, current_sample_num);
	kunmap_atomic(addr, KM_USER0);

	if (cost_accounting) {
		tmp = rshash_pos;
		/* it's sucessfully identified by random sampling
		 * hash, so increase the positive count.
		 */
		rshash_pos += rshash_cost * (HASH_STRENGTH_FULL - current_sample_num);
		BUG_ON(tmp > rshash_pos);
		calsum_count++;
	}

	return val;
}

static int memcmp_pages(struct page *page1, struct page *page2)
{
	char *addr1, *addr2;
	int ret;

	addr1 = kmap_atomic(page1, KM_USER0);
	addr2 = kmap_atomic(page2, KM_USER1);
	ret = memcmp(addr1, addr2, PAGE_SIZE);
	kunmap_atomic(addr2, KM_USER1);
	kunmap_atomic(addr1, KM_USER0);
	return ret;
}

static inline int pages_identical(struct page *page1, struct page *page2)
{
	return !memcmp_pages(page1, page2);
}

static int write_protect_page(struct vm_area_struct *vma, struct page *page,
			      pte_t *orig_pte, pte_t *old_pte)
{
	struct mm_struct *mm = vma->vm_mm;
	unsigned long addr;
	pte_t *ptep;
	spinlock_t *ptl;
	int swapped;
	int err = -EFAULT;

	addr = page_address_in_vma(page, vma);
	if (addr == -EFAULT)
		goto out;

	ptep = page_check_address(page, mm, addr, &ptl, 0);
	if (!ptep)
		goto out;

	if (old_pte)
		*old_pte = *ptep;

	if (pte_write(*ptep)) {
		pte_t entry;

		swapped = PageSwapCache(page);
		flush_cache_page(vma, addr, page_to_pfn(page));
		/*
		 * Ok this is tricky, when get_user_pages_fast() run it doesnt
		 * take any lock, therefore the check that we are going to make
		 * with the pagecount against the mapcount is racey and
		 * O_DIRECT can happen right after the check.
		 * So we clear the pte and flush the tlb before the check
		 * this assure us that no O_DIRECT can happen after the check
		 * or in the middle of the check.
		 */
		entry = ptep_clear_flush(vma, addr, ptep);
		/*
		 * Check that no O_DIRECT or similar I/O is in progress on the
		 * page
		 */
		if (page_mapcount(page) + 1 + swapped != page_count(page)) {
			set_pte_at_notify(mm, addr, ptep, entry);
			goto out_unlock;
		}

		entry = pte_wrprotect(entry);
		set_pte_at_notify(mm, addr, ptep, entry);
	}
	*orig_pte = *ptep;
	err = 0;

out_unlock:
	pte_unmap_unlock(ptep, ptl);
out:
	return err;
}

#define MERGE_ERR_PGERR		1 /* the page is invalid cannot continue */
#define MERGE_ERR_COLLI		2 /* there is a collision */
#define MERGE_ERR_CHANGED	3 /* the page has changed since lash hash */


/**
 * replace_page - replace page in vma by new ksm page
 * @vma:      vma that holds the pte pointing to page
 * @page:     the page we are replacing by kpage
 * @kpage:    the ksm page we replace page by
 * @orig_pte: the original value of the pte
 *
 * Returns 0 on success, MERGE_ERR_PGERR on failure.
 */
static int replace_page(struct vm_area_struct *vma, struct page *page,
			struct page *kpage, pte_t orig_pte)
{
	struct mm_struct *mm = vma->vm_mm;
	pgd_t *pgd;
	pud_t *pud;
	pmd_t *pmd;
	pte_t *ptep;
	spinlock_t *ptl;
	unsigned long addr;
	int err = MERGE_ERR_PGERR;

	addr = page_address_in_vma(page, vma);
	if (addr == -EFAULT)
		goto out;

	pgd = pgd_offset(mm, addr);
	if (!pgd_present(*pgd))
		goto out;

	pud = pud_offset(pgd, addr);
	if (!pud_present(*pud))
		goto out;

	pmd = pmd_offset(pud, addr);
	if (!pmd_present(*pmd))
		goto out;

	ptep = pte_offset_map_lock(mm, pmd, addr, &ptl);
	if (!pte_same(*ptep, orig_pte)) {
		pte_unmap_unlock(ptep, ptl);
		goto out;
	}

	get_page(kpage);
	page_add_anon_rmap(kpage, vma, addr);

	flush_cache_page(vma, addr, pte_pfn(*ptep));
	ptep_clear_flush(vma, addr, ptep);
	set_pte_at_notify(mm, addr, ptep, mk_pte(kpage, vma->vm_page_prot));

	page_remove_rmap(page);
	put_page(page);

	pte_unmap_unlock(ptep, ptl);
	err = 0;
out:
	return err;
}

/*
 * try_to_merge_one_page - take two pages and merge them into one
 * @vma: the vma that holds the pte pointing to page
 * @page: the PageAnon page that we want to replace with kpage
 * @kpage: the PageKsm page that we want to map instead of page,
 *         or NULL the first time when we want to use page as kpage.
 *
 * This function returns 0 if the pages were merged, -EFAULT otherwise.
 */
static int try_to_merge_one_page(struct vm_area_struct *vma, struct page *page,
				 struct page *kpage, unsigned int *same_page)
{
	//unsigned char merged = 0;
	//struct vm_area_struct *to_vma;
	//struct stable_node *node;
	//struct anon_vma *anonvma;
	pte_t orig_pte = __pte(0);
	int err = MERGE_ERR_PGERR;
	unsigned long tmp;

	if (page == kpage) {			/* ksm page forked */
		if (same_page)
			*same_page = 1;
		return 0;
	}

	if (same_page)
		*same_page = 0;


/*
	if (!(vma->vm_flags & VM_MERGEABLE))
		goto out;
*/
	if (!PageAnon(page)) {
		goto out;
	}

	/*
	 * We need the page lock to read a stable PageSwapCache in
	 * write_protect_page().  We use trylock_page() instead of
	 * lock_page() because we don't want to wait here - we
	 * prefer to continue scanning and merging different pages,
	 * then come back to this page when it is unlocked.
	 */
	if (!trylock_page(page))
		goto out;
	/*
	 * If this anonymous page is mapped only here, its pte may need
	 * to be write-protected.  If it's mapped elsewhere, all of its
	 * ptes are necessarily already write-protected.  But in either
	 * case, we need to lock and check page_count is not raised.
	 */
	if (write_protect_page(vma, page, &orig_pte, NULL) == 0) {
		if (!kpage) {
			long map_sharing = atomic_read(&page->_mapcount);
			/*
			 * While we hold page lock, upgrade page from
			 * PageAnon+anon_vma to PageKsm+NULL stable_node:
			 * stable_tree_insert() will update stable_node.
			 */
			set_page_stable_node(page, NULL);
			if (map_sharing)
				add_zone_page_state(page_zone(page),
						    NR_KSM_PAGES_SHARING,
						    map_sharing);
			mark_page_accessed(page);
			err = 0;
		} else {
			if (pages_identical(page, kpage)) {
				err = replace_page(vma, page, kpage, orig_pte);
			} else {
				if (calc_checksum(page, 0) ==
				    calc_checksum(kpage, 0)) {
					/**
					 * We compare the checksum again, to
					 * ensure that it is really a hash
					 * collision instead of being caused
					 * by page write.
					 */
					tmp = rshash_neg;
					rshash_neg += memcmp_cost;
					BUG_ON(tmp > rshash_neg);
					err = MERGE_ERR_COLLI;
				} else {
					err = MERGE_ERR_CHANGED;
				}
			}
		}
	}

	if ((vma->vm_flags & VM_LOCKED) && kpage && !err) {
		munlock_vma_page(page);
		if (!PageMlocked(kpage)) {
			unlock_page(page);
			lock_page(kpage);
			mlock_vma_page(kpage);
			page = kpage;		/* for final unlock */
		}
	}

	unlock_page(page);
	//if (merged) {
		//node = page_stable_node(page);
		//anonvma = node->old_vma
	//}
out:
	return err;
}

/*
 * try_to_merge_with_ksm_page - like try_to_merge_two_pages,
 * but no new kernel page is allocated: kpage must already be a ksm page.
 *
 * This function returns 0 if the pages were merged, -EFAULT otherwise.
 */
static int try_to_merge_with_ksm_page(struct rmap_item *rmap_item,
		struct page *page, struct page *kpage, unsigned int *same_page)
{
	struct vm_area_struct *vma = rmap_item->slot->vma;
	struct mm_struct *mm = vma->vm_mm;
	int err = MERGE_ERR_CHANGED;

	if (ksm_test_exit(mm))
		goto out;


	err = try_to_merge_one_page(vma, page, kpage, same_page);
	if (err)
		goto out;

	/* Must get reference to anon_vma while still holding mmap_sem */

out:
	return err;
}



static int restore_ksm_page_pte(struct vm_area_struct *vma, unsigned long addr,
			     pte_t orig_pte, pte_t wprt_pte)
{
	struct mm_struct *mm = vma->vm_mm;
	pgd_t *pgd;
	pud_t *pud;
	pmd_t *pmd;
	pte_t *ptep;
	spinlock_t *ptl;
	//unsigned long addr;
	int err = -EFAULT;

	pgd = pgd_offset(mm, addr);
	if (!pgd_present(*pgd))
		goto out;

	pud = pud_offset(pgd, addr);
	if (!pud_present(*pud))
		goto out;

	pmd = pmd_offset(pud, addr);
	if (!pmd_present(*pmd))
		goto out;

	ptep = pte_offset_map_lock(mm, pmd, addr, &ptl);
	if (!pte_same(*ptep, wprt_pte)) {
		/* already copied, let it be */
		pte_unmap_unlock(ptep, ptl);
		goto out;
	}

	/* Good boy, still here.
	 * When we still get the ksm page, it does not return to the free page
	 * pool, there is no way that a pte was changed to other page and gets back
	 * to this page and remind that ksm page do not reuse in do_wp_page().
	 */
	flush_cache_page(vma, addr, pte_pfn(*ptep));
	ptep_clear_flush(vma, addr, ptep);
	set_pte_at_notify(mm, addr, ptep, orig_pte);

	pte_unmap_unlock(ptep, ptl);
	err = 0;
out:
	return err;
}
/*
 * try_to_merge_two_pages - take two identical pages and prepare them
 * to be merged into one page.
 *
 * This function returns the kpage if we successfully merged two identical
 * pages into one ksm page, NULL otherwise.
 *
 * Note that this function upgrades page to ksm page: if one of the pages
 * is already a ksm page, try_to_merge_with_ksm_page should be used.
 */
static int try_to_merge_two_pages(struct rmap_item *rmap_item,
				  struct rmap_item *tree_rmap_item)
{
	pte_t orig_pte1 = __pte(0), orig_pte2 = __pte(0);
	pte_t wprt_pte1 = __pte(0), wprt_pte2 = __pte(0);
	struct vm_area_struct *vma1 = rmap_item->slot->vma;
	struct vm_area_struct *vma2 = tree_rmap_item->slot->vma;
	struct page *page = rmap_item->page;
	struct page *tree_page = tree_rmap_item->page;

	//struct mm_struct *mm1 = vma1->vm_mm;
	//struct mm_struct *mm2 = vma2->vm_mm;
	//pte_t *ptep1, *ptep2;
	//unsigned long addr1, addr2;
	//spinlock_t *ptl1, *ptl2;
	//int swapped;
	int err = MERGE_ERR_PGERR;
	unsigned long tmp;
	long map_sharing;
	struct address_space *saved_mapping;


	if (rmap_item->page == tree_rmap_item->page)
		goto out;

	if (!PageAnon(page) || !PageAnon(tree_page))
		goto out;

	lock_page(page);
	if (write_protect_page(vma1, page, &wprt_pte1, &orig_pte1) != 0) {
		unlock_page(page);
		goto out;
	}

	/*
	 * While we hold page lock, upgrade page from
	 * PageAnon+anon_vma to PageKsm+NULL stable_node:
	 * stable_tree_insert() will update stable_node.
	 */
	saved_mapping = page->mapping;
	map_sharing = atomic_read(&page->_mapcount);
	set_page_stable_node(page, NULL);
	if (map_sharing)
		add_zone_page_state(page_zone(page),
				    NR_KSM_PAGES_SHARING,
				    map_sharing);
	mark_page_accessed(page);
	unlock_page(page);

	lock_page(tree_page);
	if (write_protect_page(vma2, tree_page, &wprt_pte2, &orig_pte2) != 0) {
		unlock_page(tree_page);
		goto restore1_out;
	}

	if (pages_identical(page, tree_page)) {
		err = replace_page(vma2, tree_page, page, wprt_pte2);
		if (err)
			goto restore1_out;

		if ((vma2->vm_flags & VM_LOCKED)) {
			munlock_vma_page(tree_page);
			if (!PageMlocked(page)) {
				unlock_page(tree_page);
				lock_page(page);
				mlock_vma_page(page);
				tree_page = page;		/* for final unlock */
			}
		}

		unlock_page(tree_page);

		goto out; /* success */

	} else {
		if (calc_checksum(page, 0) ==
		    calc_checksum(tree_page, 0)) {
			/**
			 * We compare the checksum again, to
			 * ensure that it is really a hash
			 * collision instead of being caused
			 * by page write.
			 */
			tmp = rshash_neg;
			rshash_neg += memcmp_cost;
			BUG_ON(tmp > rshash_neg);
			err = MERGE_ERR_COLLI;
		} else {
			err = MERGE_ERR_CHANGED;
		}

		unlock_page(tree_page);
		goto restore1_out;
	}




/*
	int err;

	err = try_to_merge_with_ksm_page(rmap_item, page, NULL, NULL);
	if (!err) {
		err = try_to_merge_with_ksm_page(tree_rmap_item,
						tree_page, page, NULL);
		if (err)
			break_cow(rmap_item);
	}
	return err;
*/
//restore_both_out:
	/* It's ok to let tree_page write-protected, since it's not a ksm page,
	 * it will properly dealed by do_wp_page.
	 */
//	restore_page_pte(vma2, tree_rmap_item->address & PAGE_MASK,
//			 orig_pte2, wprt_pte2);
restore1_out:
	lock_page(page);
	if (!restore_ksm_page_pte(vma1, get_rmap_addr(rmap_item),
				  orig_pte1, wprt_pte1)) {
		page->mapping = saved_mapping;
	}
	unlock_page(page);
out:
	return err;
}


static inline int checksum_cmp(u32 new_val, u32 node_val)
{
	if (new_val > node_val)
		return 1;
	else if (new_val < node_val)
		return -1;
	else
		return 0;
}

/*
static inline int checksum_cmp_update(u32 checksum_val,
				      struct ksm_checksum *node_checksum,
				      struct stable_node *stable_node,
				      int *earlyexit)
{
	struct page *tree_page;
	u32 val;

	if (node_checksum->sample_num != current_sample_num) {
		if (!stable_node) {
			printk(KERN_ERR "KSM: BUG current_sample_num is %lu, while %lu is node_checksum->sample_num\n",
			       current_sample_num, node_checksum->sample_num);
			BUG();
		}

		tree_page = get_ksm_page(stable_node);
		if (!tree_page) {
			*earlyexit = 1;
			return 0;
		}

		node_checksum->val = calc_checksum(tree_page, 0);
		node_checksum->sample_num = current_sample_num;
		put_page(tree_page);
		*earlyexit = 2;
	}

	val = node_checksum->val;

	if (checksum_val > val)
		return 1;
	else if (checksum_val < val)
		return -1;
	else
		return 0;
}
*/

static inline void checksum_copy2(u32 val, struct ksm_checksum *node_checksum)
{
	node_checksum->val = val;
	node_checksum->sample_num = current_sample_num;

	return;
}



/*
 * return a non-zero hash value.
 */
static inline u32 calc_checksum_full(struct page *page, u32 checksum_old)
{
	u32 checksum_full = 0;
	void *addr;

	addr = kmap_atomic(page, KM_USER0);
	checksum_full = delta_hash(addr, current_sample_num,
				   HASH_STRENGTH_MAX, checksum_old);

	kunmap_atomic(addr, KM_USER0);

	if (!checksum_full)
		checksum_full = 1;

	return checksum_full;
}



static inline u32 rmap_item_full_hash(struct rmap_item *item, u32 checksum_val)
{
	u32 checksum_full = item->checksum_full;

	if (!checksum_full) {
		checksum_full = calc_checksum_full(item->page, checksum_val);

		item->checksum_full = checksum_full;
	}

	return checksum_full;
}



/*
 * stable_tree_search - search for page inside the stable tree
 * if return == NULL and *stable_node != NULL, it's a forked page, the stable_node is found
 * return == NULL and *stable_node == NULL, search failed
 * return != NULL and *stable_node != NULL, the stable_node is found
 * otherwise, BUG.
 */
static struct page *stable_tree_search(struct rmap_item *item, u32 checksum_val)
{
	struct rb_node *node = root_stable_treep->rb_node;
	struct tree_node *rnode;
	unsigned long checksum_full;
	struct page *page = item->page;
	struct stable_node *stable_node;

	stable_node = page_stable_node(page);
	if (stable_node) {
		/* ksm page forked, that is
		 * if (PageKsm(page) && !in_stable_tree(rmap_item))
		 * it's actually gotten once outside.
		 */
		get_page(page);
		return page;
	}

	while (node) {
		int cmp;

		rnode = rb_entry(node, struct tree_node, node);

		cmp = checksum_cmp(checksum_val, rnode->checksum_val);

		if (cmp < 0) {
			node = node->rb_left;
		} else if (cmp > 0) {
			node = node->rb_right;
		} else
			break;
	}

	if (!node)
		return NULL;

	if (rnode->count == 1) {
		stable_node = rb_entry(rnode->sub_root.rb_node,
				       struct stable_node, node);
		BUG_ON(!stable_node);

		goto get_page_out;
	}

	/* ok, we have to search the collision subtree,
	 * hash the page to a full strength.
	 */
	node = rnode->sub_root.rb_node;
	BUG_ON(!node);
	checksum_full = rmap_item_full_hash(item, checksum_val);

	while (node) {
		int cmp;

		stable_node = rb_entry(node, struct stable_node, node);

		cmp = checksum_cmp(checksum_full, stable_node->checksum_full);

		if (cmp < 0) {
			node = node->rb_left;
		} else if (cmp > 0) {
			node = node->rb_right;
		} else
			goto get_page_out;
	}

	return NULL;

get_page_out:
	page = get_ksm_page(stable_node, 1);
	return page;
}

/*
 * oldpage is already locked.
 */
static void try_to_merge_with_tree_page(struct rmap_item *item1,
				       struct rmap_item *item2,
				       struct page *oldpage,
				       struct page *tree_page,
				       int *success1,
				       int *success2)
{
	//pte_t orig_pte1 = __pte(0), orig_pte2 = __pte(0);
	spinlock_t *ptl1, *ptl2;
	pte_t *ptep1, *ptep2;
	unsigned long addr1, addr2;
	struct vm_area_struct *vma1 = item1->slot->vma;
	struct vm_area_struct *vma2 = item2->slot->vma;

	*success1 = 0;
	*success2 = 0;

	if (unlikely(oldpage == tree_page)) {
		/* I don't think this can really happen */
		goto success_both;
	}

	if (!PageAnon(oldpage) || !PageKsm(oldpage)) {
		goto failed;
	}

	/* If the oldpage is still ksm and still pointed
	 * to in the right place, and still write protected,
	 * we are confident it's not changed, no need to
	 * memcmp anymore.
	 * be ware, we cannot take nested pte locks,
	 * deadlock risk.
	 */
	addr1 = get_rmap_addr(item1);

	ptep1 = page_check_address(oldpage, vma1->vm_mm, addr1, &ptl1, 0);
	if (!ptep1)
		goto failed;

	if (pte_write(*ptep1)) {
		/* has changed, abort! */
		pte_unmap_unlock(ptep1, ptl1);
		goto failed;
	}

	//orig_pte1 = *ptep1;

	get_page(tree_page);
	page_add_anon_rmap(tree_page, vma1, addr1);

	flush_cache_page(vma1, addr1, pte_pfn(*ptep1));
	ptep_clear_flush(vma1, addr1, ptep1);
	set_pte_at_notify(vma1->vm_mm, addr1, ptep1, mk_pte(tree_page, vma1->vm_page_prot));

	page_remove_rmap(oldpage);
	put_page(oldpage);

	pte_unmap_unlock(ptep1, ptl1);


	/* ok, then vma2, remind that pte1 already set */
	addr2 = get_rmap_addr(item2);

	ptep2 = page_check_address(oldpage, vma2->vm_mm, addr2, &ptl2, 0);
	if (!ptep2)
		goto success1;

	if (pte_write(*ptep2)) {
		/* has changed, abort! */
		pte_unmap_unlock(ptep2, ptl2);
		goto success1;
	}

	get_page(tree_page);
	page_add_anon_rmap(tree_page, vma2, addr2);

	flush_cache_page(vma2, addr2, pte_pfn(*ptep2));
	ptep_clear_flush(vma2, addr2, ptep2);
	set_pte_at_notify(vma2->vm_mm, addr2, ptep2, mk_pte(tree_page, vma2->vm_page_prot));

	page_remove_rmap(oldpage);
	put_page(oldpage);

	pte_unmap_unlock(ptep2, ptl2);


success_both:
	printk(KERN_ERR "KSM: both success!\n");
	*success2 = 1;
success1:
	*success1 = 1;

	if ((*success1 && vma1->vm_flags & VM_LOCKED) ||
	    (*success2 && vma2->vm_flags & VM_LOCKED)) {
		munlock_vma_page(oldpage);
		if (!PageMlocked(tree_page)) {

			/*ok, we do not need oldpage any more in the caller
			 * we can break the lock now.
			 */
			unlock_page(oldpage);
			lock_page(tree_page);
			mlock_vma_page(tree_page);
			unlock_page(tree_page);
			lock_page(oldpage); // unlocked outside
		}
	}


failed:
	return;
}



/* We remap the full hash value 0 to 1
 * 0 is used for a tag that this hash value is not initialized.
 */
static inline void stable_node_full_hash(struct stable_node *node,
					struct page *page, u32 checksum_val)
{
	u32 checksum_full = node->checksum_full;

	if (!checksum_full) {
		checksum_full = calc_checksum_full(page, checksum_val);
		node->checksum_full = checksum_full;
	}
}

static void print_page(struct page *pg)
{
	void *addr;
	int i;
	u32 *key;

	printk(KERN_ERR "KSM: page %p------------------------------------\n", pg);
	addr = kmap_atomic(pg, KM_USER0);
	key = (u32*)addr;

	for (i=0; i<PAGE_SIZE/sizeof(u32); i++) {
		printk(KERN_ERR "%x ", key[i]);
	}
	kunmap_atomic(addr, KM_USER0);
}

/*
 * stable_tree_insert - insert rmap_item pointing to new ksm page
 * into the stable tree.
 *
 * This function returns the stable tree node just allocated on success,
 * NULL otherwise.
 */
static struct stable_node *
stable_tree_insert(struct page *kpage, u32 checksum_val,
		   struct rmap_item *rmap_item,
		   struct rmap_item *tree_rmap_item,
		   int *success1, int *success2)
{
	struct rb_node **new = &root_stable_treep->rb_node;
	struct rb_node *parent = NULL, *sparent;
	struct stable_node *stable_node, *new_stable_node;
	struct tree_node *rnode;
	struct page *tree_page;
	u32 checksum_full = 0;
	int cmp;

	*success1 = *success2 = 0;

	while (*new) {
		//struct rmap_item *tree_rmap_item;
		//
		int cmp;

		rnode = rb_entry(*new, struct tree_node, node);

		cmp = checksum_cmp(checksum_val, rnode->checksum_val);

		if (cmp < 0) {
			parent = *new;
			new = &parent->rb_left;
		} else if (cmp > 0) {
			parent = *new;
			new = &parent->rb_right;
		} else
			break;
	}

	if (*new) {
		/* find a stable tree node with same hash value */
		if (rnode->count == 1) {
			stable_node = rb_entry(rnode->sub_root.rb_node,
					       struct stable_node, node);

			tree_page = get_ksm_page(stable_node, 0);
			if (tree_page) {
				cmp = memcmp_pages(kpage, tree_page);
				if (!cmp)
					goto try_to_merge;
				else {
					put_page(tree_page);

					stable_node_full_hash(stable_node, tree_page,
							      rnode->checksum_val);
					checksum_full =
						rmap_item_full_hash(rmap_item,
								    checksum_val);

					cmp = checksum_cmp(checksum_full,
						stable_node->checksum_full);
					parent = &stable_node->node;
					if (cmp < 0) {
						new = &parent->rb_left;
					} else if (cmp > 0) {
						new = &parent->rb_right;
					} else {
						printk(KERN_ERR "KSM collision1 "
								"checksum_full=%lu\n",
						       checksum_full);
						goto failed;
					}

					goto new_stable_node;
				}
			} else {
				/* the only stable_node deleted, the tree node
				 * was also deleted. We reuse its tree_node.
				 */
				goto tree_node_reuse;
			}
		}

	research:
		/* well, search the collision subtree */
		new = &rnode->sub_root.rb_node;
		parent = NULL;
		BUG_ON(!*new);
		checksum_full = rmap_item_full_hash(rmap_item, checksum_val);
		while (*new) {
			int cmp;
			u32 check1, check2, sample_num_save;

			stable_node = rb_entry(*new, struct stable_node, node);

			cmp = checksum_cmp(checksum_full, stable_node->checksum_full);

			if (cmp < 0) {
				parent = *new;
				new = &parent->rb_left;
			} else if (cmp > 0) {
				parent = *new;
				new = &parent->rb_right;
			} else {
				tree_page = get_ksm_page(stable_node, 0);
				if (tree_page) {
					cmp = memcmp_pages(kpage, tree_page);
					if (!cmp)
						goto try_to_merge;
					else {
/*
						printk(KERN_ERR "KSM collision2 checksum_full_page=%u ck_full_treepage=%u\n",
						calc_checksum_full(kpage, checksum_val), calc_checksum_full(tree_page, checksum_val));
						sample_num_save = current_sample_num;
						current_sample_num = HASH_STRENGTH_FULL;
						check1 = calc_checksum(kpage, 0);
						check2 = calc_checksum(tree_page, 0);
						printk(KERN_ERR "KSM real ck1=%u, ck2=%u pg1=%p pg2=%p\n",
						       check1, check2, kpage, tree_page);
						print_page(kpage);
						print_page(tree_page);
						current_sample_num = sample_num_save;
*/

						put_page(tree_page);
						goto failed;
					}
				} else {
					/* stable node may be deleted,
					 * and tree maybe restructed,
					 * cannot continue;
					 * research it.
					 */
					printk(KERN_ERR "KSM collision3 checksum_full=%lu\n",
					       checksum_full);
					if (rnode->count)
						goto research;
					else
						goto tree_node_reuse;
				}
			}
		}

		goto new_stable_node;
	}

	/* no tree node found */
	rnode = alloc_tree_node(stable_tree_node_listp);
	if (!rnode)
		goto failed;
	else {
		rnode->checksum_val = checksum_val;
		rb_link_node(&rnode->node, parent, new);
		rb_insert_color(&rnode->node, root_stable_treep);
tree_node_reuse:
		/* prepare for stable node insertion */
		parent = NULL;
		new = &rnode->sub_root.rb_node;
	}


new_stable_node:
	new_stable_node = alloc_stable_node();
	if (!new_stable_node)
		goto failed;

	new_stable_node->kpfn = page_to_pfn(kpage);
	new_stable_node->checksum_full = checksum_full;
	new_stable_node->tree_node = rnode;
	set_page_stable_node(kpage, new_stable_node);

	rb_link_node(&new_stable_node->node, parent, new);
	rb_insert_color(&new_stable_node->node, &rnode->sub_root);
	rnode->count++;
	*success1 = *success2 = 1;
	return new_stable_node;


try_to_merge:
	/**
	 * If ret==0, they are really the same, try to merge.
	 * We have both the rmap_items' mmap_sem already locked
	 * and the page gotten and locked and , easy to do the job.
	 */
	try_to_merge_with_tree_page(rmap_item, tree_rmap_item, kpage,
				    tree_page, success1, success2);
	put_page(tree_page);
	if (!*success1 && !*success2) {
		printk(KERN_ERR "KSM really the same failed\n");

		goto failed;
	} else
		return stable_node;


failed:
	return NULL;
}

/*
 * unstable_tree_search_insert - search for identical page,
 * else insert rmap_item into the unstable tree.
 *
 * This function searches for a page in the unstable tree identical to the
 * page currently being scanned; and if no identical page is found in the
 * tree, we insert rmap_item as a new object into the unstable tree.
 *
 * This function returns pointer to rmap_item found to be identical
 * to the currently scanned page, NULL otherwise.
 *
 * This function does both searching and inserting, because they share
 * the same walking algorithm in an rbtree.
 */
static
struct rmap_item *unstable_tree_search_insert(struct rmap_item *rmap_item,
					      u32 checksum_val)

{
	struct rb_node **new = &root_unstable_tree.rb_node;
	struct rb_node *parent = NULL;
	struct tree_node *rnode;
	u32 checksum_full;
	struct rmap_item *tree_rmap_item;
	//struct page *page = rmap_item->page;

	while (*new) {
		//struct rmap_item *tree_rmap_item;
		//struct page *tree_page;
		int cmp;

		rnode = rb_entry(*new, struct tree_node, node);

		cmp = checksum_cmp(checksum_val, rnode->checksum_val);

		if (cmp < 0) {
			parent = *new;
			new = &parent->rb_left;
		} else if (cmp > 0) {
			parent = *new;
			new = &parent->rb_right;
		} else
			break;
	}

	if (*new) {
		/* got the tree_node */
		if (rnode->count == 1) {
			tree_rmap_item = rb_entry(rnode->sub_root.rb_node,
						  struct rmap_item, node);
			BUG_ON(!tree_rmap_item);

			goto get_page_out;
		}

		/* well, search the collision subtree */
		new = &rnode->sub_root.rb_node;
		BUG_ON(!*new);
		checksum_full = rmap_item_full_hash(rmap_item, checksum_val);

		while (*new) {
			int cmp;

			tree_rmap_item = rb_entry(*new, struct rmap_item, node);

			cmp = checksum_cmp(checksum_full, tree_rmap_item->checksum_full);
			parent = *new;
			if (cmp < 0) {
				new = &parent->rb_left;
			} else if (cmp > 0) {
				new = &parent->rb_right;
			} else
				goto get_page_out;
		}
	} else {
		/* alloc a new tree_node */
		rnode = alloc_tree_node(&unstable_tree_node_list);
		if (!rnode)
			return NULL;

		rnode->checksum_val = checksum_val;
		rb_link_node(&rnode->node, parent, new);
		rb_insert_color(&rnode->node, &root_unstable_tree);
		parent = NULL;
		new = &rnode->sub_root.rb_node;
	}

	/* did not found even in sub-tree */
	rmap_item->tree_node = rnode;
	rmap_item->address |= UNSTABLE_FLAG;
	rmap_item->append_round = ksm_scan_round;
	rb_link_node(&rmap_item->node, parent, new);
	rb_insert_color(&rmap_item->node, &rnode->sub_root);

	/* all link related members should be initialized
	 * because we use root_unstable_tree = RB_ROOT to
	 * clear all nodes.
	 */
	ksm_pages_unshared++;
	return NULL;

get_page_out:
	if (tree_rmap_item->page == rmap_item->page)
		return NULL;

	if (get_tree_rmap_item_page(tree_rmap_item))
		return NULL;

	return tree_rmap_item;
}

static void enter_inter_vma_table(struct vma_slot *slot)
{
	unsigned int i;

	for (i = 0; i <= ksm_vma_table_size; i++) {
		if (!ksm_vma_table[i])
			break;
	}
	BUG_ON(ksm_vma_table[i]);
	slot->ksm_index = i;
	ksm_vma_table[i] = slot;
	ksm_vma_table_num++;

	BUG_ON(i > ksm_vma_table_index_end);
	if (i == ksm_vma_table_index_end)
		ksm_vma_table_index_end++;

	BUG_ON(ksm_vma_table_index_end > ksm_vma_table_size - 1);
}

static inline void inc_vma_intertab_pair(struct vma_slot *slot1,
					 struct vma_slot *slot2)
{
	unsigned long offset;

	if (slot1->ksm_index == -1)
		enter_inter_vma_table(slot1);

	if (slot2->ksm_index == -1)
		enter_inter_vma_table(slot2);

	offset = intertab_vma_offset(slot1->ksm_index, slot2->ksm_index);
	ksm_inter_vma_table[offset]++;
	BUG_ON(!ksm_inter_vma_table[offset]);
}

static inline void dec_vma_intertab_pair(struct vma_slot *slot1,
					 struct vma_slot *slot2)
{
	unsigned long offset;
	BUG_ON(slot1->ksm_index == -1 || slot2->ksm_index == -1);

	offset = intertab_vma_offset(slot1->ksm_index, slot2->ksm_index);
	BUG_ON(!ksm_inter_vma_table[offset]);
	ksm_inter_vma_table[offset]--;
}


/*
 * stable_tree_append - add another rmap_item to the linked list of
 * rmap_items hanging off a given node of the stable tree, all sharing
 * the same ksm page.
 */
static void stable_tree_append(struct rmap_item *rmap_item,
			       struct stable_node *stable_node)
{
	struct node_vma *node_vma = NULL, *new_node_vma, *node_vma_iter = NULL;
	struct hlist_node *hlist, *cont_p;
	unsigned long key = (unsigned long)rmap_item->slot;

	//rmap_item->head = stable_node;
	BUG_ON(!stable_node);
	rmap_item->address |= STABLE_FLAG;
	rmap_item->append_round = ksm_scan_round;

	if (hlist_empty(&stable_node->hlist)) {
		ksm_pages_shared++;
		goto node_vma_new;
	} else
		ksm_pages_sharing++;

	hlist_for_each_entry(node_vma, hlist, &stable_node->hlist, hlist) {
		if (node_vma->last_update == ksm_scan_round) {
			inc_vma_intertab_pair(rmap_item->slot, node_vma->slot);
		}
		if (node_vma->key >= key)
			break;
	}

	cont_p = hlist;

	if (node_vma && node_vma->key == key) {
		if (node_vma->last_update == ksm_scan_round) {
			/**
			 * we consider this page a inner duplicate, cancel
			 * other updates
			 */
			hlist_for_each_entry(node_vma_iter, hlist,
					     &stable_node->hlist, hlist) {
				if (node_vma_iter->key == key)
					break;

				/* only need to increase the same vma */
				if (node_vma_iter->last_update == ksm_scan_round) {
					dec_vma_intertab_pair(rmap_item->slot,
							      node_vma_iter->slot);
				}
			}
		} else {
			/**
			 * Although it's same vma, it contains no duplicate for this
			 * round. Continue scan other vma.
			 */
			hlist_for_each_entry_continue(node_vma_iter, hlist, hlist) {
				if (node_vma_iter->last_update == ksm_scan_round) {
					inc_vma_intertab_pair(rmap_item->slot,
							      node_vma_iter->slot);
				}
			}

		}

		goto node_vma_ok;
	}

node_vma_new:
	/* no same vma already in node, alloc a new node_vma */
	new_node_vma = alloc_node_vma();
	BUG_ON(!new_node_vma);
	new_node_vma->head = stable_node;
	new_node_vma->slot = rmap_item->slot;

	if (!node_vma) {
		hlist_add_head(&new_node_vma->hlist, &stable_node->hlist);
	} else if (node_vma->key != key) {
		if (node_vma->key < key)
			hlist_add_after(&node_vma->hlist, &new_node_vma->hlist);
		else {
			hlist_for_each_entry_continue(node_vma_iter, cont_p, hlist) {
				if (node_vma_iter->last_update == ksm_scan_round) {
					inc_vma_intertab_pair(rmap_item->slot,
							      node_vma_iter->slot);
				}
			}
			hlist_add_before(&new_node_vma->hlist, &node_vma->hlist);
		}

	}
	node_vma = new_node_vma;

node_vma_ok: /* ok, ready to add to the list */
	rmap_item->head = node_vma;
	hlist_add_head(&rmap_item->hlist, &node_vma->rmap_hlist);
	node_vma->last_update = ksm_scan_round;
	hold_anon_vma(rmap_item, rmap_item->slot->vma->anon_vma);
}


/*
 * cmp_and_merge_page - first see if page can be merged into the stable tree;
 * if not, compare checksum to previous and if it's the same, see if page can
 * be inserted into the unstable tree, or merged with a page already there and
 * both transferred to the stable tree.
 *
 * @page: the page that we are searching identical page to.
 * @rmap_item: the reverse mapping into the virtual address of this page
 */
static void cmp_and_merge_page(struct rmap_item *rmap_item)
{
	struct rmap_item *tree_rmap_item;
	struct page *page;
	//struct stable_node *stable_node;
	struct page *kpage = NULL;
	u32 checksum_val, checksum_full;
	int err;
	unsigned int success1, success2;
	struct stable_node *snode;
	int same_page = 0, cmp;
	struct rb_node *parent = NULL, **new;

	remove_rmap_item_from_tree(rmap_item);

	page = rmap_item->page;
	checksum_val = calc_checksum(page, 1);

	ksm_pages_round_scanned++;

	/* We first start with searching the page inside the stable tree */
	kpage = stable_tree_search(rmap_item, checksum_val);
	if (kpage) {
		err = try_to_merge_with_ksm_page(rmap_item, page,
						 kpage, &same_page);
		if (!err) {
			/*
			 * The page was successfully merged:
			 * add its rmap_item to the stable tree.
			 */
			/* we don't lock page because we've gotten kpage,
			 */
			stable_tree_append(rmap_item, page_stable_node(kpage));
			put_page(kpage);
			return; /* success */

		}
		put_page(kpage);
		/* we let it go on search the unstable tree because
		 * it may fail on hash collision.
		 */
	}

	/*
	 * If the hash value of the page has changed from the last time
	 * we calculated it, this page is changing frequently: therefore we
	 * don't want to insert it in the unstable tree, and we don't want
	 * to waste our time searching for something identical to it there.
	 *
	 *  checksum compare is disabled and left it to thrashing area detection
	 */
	/*
	cmp = checksum_compare(rmap_item->oldchecksum, checksum);
	if (cmp) {
		checksum_copy2(checksum, rmap_item->oldchecksum);
		return;
	}*/


	tree_rmap_item =
		unstable_tree_search_insert(rmap_item, checksum_val);
	if (tree_rmap_item) {
		err = try_to_merge_two_pages(rmap_item, tree_rmap_item);
		/*
		 * As soon as we merge this page, we want to remove the
		 * rmap_item of the page we have merged with from the unstable
		 * tree, and insert it instead as new node in the stable tree.
		 */
		if (!err) {
/*
			update_intertab_unstable(rmap_item, tree_rmap_item);
*/
			kpage = page;
			remove_rmap_item_from_tree(tree_rmap_item);
			lock_page(kpage);
			snode = stable_tree_insert(kpage, checksum_val,
						   rmap_item, tree_rmap_item,
						   &success1, &success2);
			unlock_page(kpage);

			if (success1)
				stable_tree_append(rmap_item, snode);
			else{
				printk(KERN_ERR "KSM: failed success1 on page=%p\n", page);
				break_cow(rmap_item);
			}

			if (success2)
				stable_tree_append(tree_rmap_item, snode);
			else {
				printk(KERN_ERR "KSM: failed success2 on page=%p\n", page);
				break_cow(tree_rmap_item);
			}

		} else if (err == MERGE_ERR_COLLI) {
			if (tree_rmap_item->tree_node->count == 1) {
				rmap_item_full_hash(tree_rmap_item,
				tree_rmap_item->tree_node->checksum_val);
			} else
				BUG_ON(!(tree_rmap_item->checksum_full));
			checksum_full = rmap_item_full_hash(rmap_item, checksum_val);
			cmp = checksum_cmp(checksum_full, tree_rmap_item->checksum_full);
			parent = &tree_rmap_item->node;
			if (cmp < 0) {
				new = &parent->rb_left;
			} else if (cmp > 0) {
				new = &parent->rb_right;
			} else
				goto up_out;

			rmap_item->tree_node = tree_rmap_item->tree_node;
			rmap_item->address |= UNSTABLE_FLAG;
			rmap_item->append_round = ksm_scan_round;
			rb_link_node(&rmap_item->node, parent, new);
			rb_insert_color(&rmap_item->node, &tree_rmap_item->tree_node->sub_root);
		}


		put_page(tree_rmap_item->page);

up_out:
		up_read(&tree_rmap_item->slot->vma->vm_mm->mmap_sem);
	}
}

static inline unsigned long get_pool_index(struct vma_slot *slot,
					   unsigned long index)
{
	unsigned long pool_index;

	pool_index = (sizeof(struct rmap_list_entry *) * index) >> PAGE_SHIFT;
	if (pool_index >= slot->pool_size)
		BUG();
	return pool_index;
}

static inline unsigned long index_page_offset(unsigned long index)
{
	return offset_in_page(sizeof(struct rmap_list_entry *) * index);
}

static inline
struct rmap_list_entry *get_rmap_list_entry(struct vma_slot *slot,
					    unsigned long index, int need_alloc)
{
	unsigned long pool_index;
	void *addr;


	pool_index = get_pool_index(slot, index);
	if (!slot->rmap_list_pool[pool_index]) {
		if (!need_alloc)
			return NULL;

		slot->rmap_list_pool[pool_index] =
			alloc_page(GFP_KERNEL | __GFP_ZERO);
		BUG_ON(!slot->rmap_list_pool[pool_index]);
	}

	addr = kmap(slot->rmap_list_pool[pool_index]);
	addr += index_page_offset(index);

	return addr;
}

static inline void put_rmap_list_entry(struct vma_slot *slot,
				       unsigned long index)
{
	unsigned long pool_index;

	pool_index = get_pool_index(slot, index);
	BUG_ON(!slot->rmap_list_pool[pool_index]);
	kunmap(slot->rmap_list_pool[pool_index]);
}

static inline int entry_is_new(struct rmap_list_entry *entry)
{
	return (!entry->item);
}

/*
static inline int entry_is_addr(struct rmap_list_entry *entry)
{
	return (entry->is_addr && entry->addr);
}

static inline int entry_is_item(struct rmap_list_entry *entry)
{
	BUG_ON(!entry->is_addr)
	return (!entry->is_addr)
}
*/

static inline unsigned long get_index_orig_addr(struct vma_slot *slot,
						unsigned long index)
{
	return (slot->vma->vm_start + (index << PAGE_SHIFT));
}

static inline unsigned long get_entry_address(struct rmap_list_entry *entry)
{
	unsigned long addr;

	if (is_addr(entry->addr)) {
		addr = get_clean_addr(entry->addr);
	} else if (entry->item) {
		addr = get_rmap_addr(entry->item);
	} else
		BUG();

	return addr;
}

static inline struct rmap_item *get_entry_item(struct rmap_list_entry *entry)
{
	if (is_addr(entry->addr))
		return NULL;

	return entry->item;
}

static inline void inc_rmap_list_pool_count(struct vma_slot *slot,
					    unsigned long index)
{
	unsigned long pool_index;

	pool_index = get_pool_index(slot, index);
	BUG_ON(!slot->rmap_list_pool[pool_index]);
	slot->pool_counts[pool_index]++;
}

static inline void dec_rmap_list_pool_count(struct vma_slot *slot,
					    unsigned long index)
{
	unsigned long pool_index;

	pool_index = get_pool_index(slot, index);
	BUG_ON(!slot->rmap_list_pool[pool_index]);
	BUG_ON(!slot->pool_counts[pool_index]);
	slot->pool_counts[pool_index]--;
}

static inline int entry_has_rmap(struct rmap_list_entry *entry)
{
	return (!is_addr(entry->addr) && entry->item);
}

static inline void swap_entries(struct rmap_list_entry *entry1,
				unsigned long index1,
				struct rmap_list_entry *entry2,
				unsigned long index2)
{
	struct rmap_list_entry tmp;

	/* swapping two new entries is meaningless */
	BUG_ON(entry_is_new(entry1) && entry_is_new(entry2));

	tmp = *entry1;
	*entry1 = *entry2;
	*entry2 = tmp;

	if (entry_has_rmap(entry1)) {
		entry1->item->entry_index = index1;
	}

	if (entry_has_rmap(entry2)) {
		entry2->item->entry_index = index2;
	}

	if (entry_has_rmap(entry1) && !entry_has_rmap(entry2)) {
		inc_rmap_list_pool_count(entry1->item->slot, index1);
		dec_rmap_list_pool_count(entry1->item->slot, index2);
	} else if (!entry_has_rmap(entry1) && entry_has_rmap(entry2)) {
		inc_rmap_list_pool_count(entry2->item->slot, index2);
		dec_rmap_list_pool_count(entry2->item->slot, index1);
	}
}



static inline void free_entry_item(struct rmap_list_entry *entry)
{
	unsigned long index;
	struct rmap_item *item;

	if (!is_addr(entry->addr)) {
		BUG_ON(!entry->item);
		item = entry->item;
		entry->addr = get_rmap_addr(item);
		set_is_addr(entry->addr);
		index = item->entry_index;
		remove_rmap_item_from_tree(item);
		dec_rmap_list_pool_count(item->slot, index);
		free_rmap_item(item);
	}
}

static inline int pool_entry_boundary(unsigned long index)
{
	unsigned long linear_addr;

	linear_addr = sizeof(struct rmap_list_entry *) * index;
	return (index && !offset_in_page(linear_addr));
}

static inline void try_free_last_pool(struct vma_slot *slot,
				      unsigned long index)
{
	unsigned long pool_index;

	pool_index = get_pool_index(slot, index);
	if (slot->rmap_list_pool[pool_index] && !slot->pool_counts[pool_index]) {
		__free_page(slot->rmap_list_pool[pool_index]);
		slot->rmap_list_pool[pool_index] = NULL;
		slot->need_sort = 1;
	}

}

static inline unsigned long vma_item_index(struct vm_area_struct *vma,
					   struct rmap_item *item)
{
	return ((get_rmap_addr(item) - vma->vm_start) >> PAGE_SHIFT);
}

static int within_same_pool(struct vma_slot *slot,
			    unsigned long i, unsigned long j)
{
	unsigned long pool_i, pool_j;

	pool_i = get_pool_index(slot, i);
	pool_j = get_pool_index(slot, j);

	return (pool_i == pool_j);
}

static void sort_rmap_entry_list(struct vma_slot *slot)
{
	unsigned long i, j;
	struct rmap_list_entry *entry, *swap_entry;

	//printk(KERN_ERR "KSM: sort list of vma=%x slot->pages_scanned=%lu\n", (unsigned int)slot->vma, slot->pages_scanned);

	entry = get_rmap_list_entry(slot, 0, 0);
	for (i = 0; i < slot->pages; ) {

		if (!entry)
			goto skip_whole_pool;

		if (entry_is_new(entry))
			goto next_entry;

		if (is_addr(entry->addr)) {
			entry->addr = 0;
			goto next_entry;
		}

		j = vma_item_index(slot->vma, entry->item);
		if ( j == i)
			goto next_entry;

		if (within_same_pool(slot, i, j))
			swap_entry = entry + j - i;
		else {
			swap_entry = get_rmap_list_entry(slot, j, 1);
		}
		swap_entries(entry, i, swap_entry, j);
		if (!within_same_pool(slot, i, j))
			put_rmap_list_entry(slot, j);
		continue;

skip_whole_pool:
		i += PAGE_SIZE / sizeof(*entry);
		if (i < slot->pages)
			entry = get_rmap_list_entry(slot, i, 0);
		continue;

next_entry:
		if (i >= slot->pages - 1 ||
		    !within_same_pool(slot, i, i + 1)) {
			put_rmap_list_entry(slot, i);
			if (i + 1 < slot->pages)
				entry = get_rmap_list_entry(slot, i + 1, 0);
		} else
			entry++;
		i++;
		continue;
	}

	/* free empty pool entries which contain no rmap_item */
	/* CAN be simplied to based on only pool_counts when bug freed !!!!! */
	for (i = 0; i < slot->pool_size; i++) {
		unsigned char has_rmap;
		void *addr;

		if (!slot->rmap_list_pool[i])
			continue;

		has_rmap = 0;
		addr = kmap(slot->rmap_list_pool[i]);
		BUG_ON(!addr);
		for (j = 0; j < PAGE_SIZE / sizeof(*entry); j++) {
			entry = (struct rmap_list_entry *)addr + j;
			if (is_addr(entry->addr))
				continue;
			if (!entry->item)
				continue;
			has_rmap = 1;
		}
		kunmap(slot->rmap_list_pool[i]);
		if (!has_rmap) {
			BUG_ON(slot->pool_counts[i]);
			__free_page(slot->rmap_list_pool[i]);
			slot->rmap_list_pool[i] = NULL;
		}
	}

	slot->need_sort = 0;
}

static inline int vma_fully_scanned(struct vma_slot *slot)
{
	return (slot->pages_scanned && !(slot->pages_scanned % slot->pages));
}

static struct rmap_item *get_next_rmap_item(struct vma_slot *slot)
{
	unsigned long rand_range, addr, swap_index, scan_index;
	struct rmap_item *item = NULL;
	struct rmap_list_entry *scan_entry, *swap_entry = NULL;
	struct page *page;

	scan_index = swap_index = slot->pages_scanned % slot->pages;

	if (pool_entry_boundary(scan_index))
		try_free_last_pool(slot, scan_index - 1);

	if (vma_fully_scanned(slot)){
		slot->need_rerand = slot->need_sort;
		if (slot->need_sort) {
			sort_rmap_entry_list(slot);
		}
	}

	scan_entry = get_rmap_list_entry(slot, scan_index, 1);
	if (entry_is_new(scan_entry)) {
		scan_entry->addr = get_index_orig_addr(slot, scan_index);
		set_is_addr(scan_entry->addr);
	}

	if (slot->need_rerand) {
		rand_range = slot->pages - scan_index;
		BUG_ON(!rand_range);
		swap_index = scan_index + (random32() % rand_range);
	}

	if (swap_index != scan_index) {
		//// if swap entry and scan entry is within same pool
		swap_entry = get_rmap_list_entry(slot, swap_index, 1);
		if (entry_is_new(swap_entry)) {
			swap_entry->addr = get_index_orig_addr(slot, swap_index);
			set_is_addr(swap_entry->addr);
		}
		swap_entries(scan_entry, scan_index, swap_entry, swap_index);
	}


	addr = get_entry_address(scan_entry);
	item = get_entry_item(scan_entry);


/*
	printk(KERN_ERR "KSM: scan task=%s vma=%x page_index=%lu scan_index=%lu swap_index=%lu\n",
	       vma->vm_mm->owner->comm, (unsigned int)vma, (addr - vma->vm_start) >> PAGE_SHIFT, scan_index, swap_index);
*/



	BUG_ON(addr > slot->vma->vm_end || addr < slot->vma->vm_start );


	page = follow_page(slot->vma, addr, FOLL_GET);

	if (!page)
		goto nopage;

	if (!PageAnon(page)) {
		goto putpage;
	}

	flush_anon_page(slot->vma, page, addr);
	flush_dcache_page(page);

	if (!item) {
		item = alloc_rmap_item();
		if (item) {
			/* It has already been zeroed */
			item->slot = slot;
			item->address = addr;
			item->entry_index = scan_index;
			scan_entry->item = item;
			inc_rmap_list_pool_count(slot, scan_index);
		} else
			goto putpage;
	}

	BUG_ON(item->slot != slot);
	/* the page may have changed */
	item->page = page;
	put_rmap_list_entry(slot, scan_index);
	if (swap_entry)
		put_rmap_list_entry(slot, swap_index);
	return item;

putpage:
	put_page(page);
	page = NULL;
nopage:
	/* no page, store addr back and free rmap_item if possible */
	free_entry_item(scan_entry);
	put_rmap_list_entry(slot, scan_index);
	if (swap_entry)
		put_rmap_list_entry(slot, swap_index);
	return NULL;
}
/*
static struct rmap_item *get_next_rmap_item(struct vm_area_struct *vma,
					    unsigned long addr)
{
	struct rmap_item *rmap_item, *rmap_item_old , *rmap_item_new;

	rmap_item = vma->rmap_list;
	rmap_item_old = NULL;

	while (rmap_item) {
		if ((rmap_item->address & PAGE_MASK) == addr)
			return rmap_item;

		if (rmap_item->address > addr)
			break;

		rmap_item_old = rmap_item;
		rmap_item = rmap_item->rmap_list;
	}

	rmap_item_new = alloc_rmap_item();
	if (rmap_item_new) {
		rmap_item_new->vma = vma;
		rmap_item_new->address = addr;
		rmap_item_new->rmap_list = rmap_item;

		if (rmap_item_old)
			rmap_item_old->rmap_list = rmap_item_new;
		else
			vma->rmap_list = rmap_item_new;
		rmap_item = rmap_item_new;
		vma->rmap_num++;
	}
	return rmap_item;
}
*/


/**
 * Called with mmap_sem locked.
 *
 *
 * @param slot
 */
static void scan_vma_one_page(struct vma_slot *slot)
{
	struct mm_struct *mm;
	//struct page *page = NULL;
	struct rmap_item *rmap_item = NULL;
	struct vm_area_struct *vma = slot->vma;

	mm = vma->vm_mm;
	BUG_ON(!mm);
	BUG_ON(!slot);

/*
	pages = vma_pages(vma);

	do {
		addr = vma->vm_start + (random32() % pages) * PAGE_SIZE;
		repeats++;
	} while (rmap_item->last_scan == slot->rung->scan_turn &&
		 repeats <= pages * 2);
*/

	rmap_item = get_next_rmap_item(slot);
	if (!rmap_item) {
		//BUG_ON(page);
		goto out1;
	}


	if (PageKsm(rmap_item->page) && in_stable_tree(rmap_item))
		goto out2;

	cmp_and_merge_page(rmap_item);
out2:
	put_page(rmap_item->page);
out1:
	//rmap_item->last_scan = slot->rung->scan_turn;
	slot->rung->pages_to_scan--;
	slot->pages_scanned++;
	slot->slot_scanned = 1;
	if (vma_fully_scanned(slot)) {
		slot->fully_scanned = 1;
		slot->rung->fully_scanned_slots++;
		BUG_ON(!slot->rung->fully_scanned_slots);
	}
}

static unsigned long get_vma_random_scan_num(struct vma_slot *slot,
					     unsigned long scan_ratio)
{
	//unsigned long needed;

	return (slot->pages * scan_ratio / KSM_SCAN_RATIO_MAX);
/*
	if (!needed)
		return 0;

        return get_random_sample_num(vma_pages(vma), needed);
*/
}

static inline void vma_rung_enter(struct vma_slot *slot,
				  struct scan_rung *rung)
{
	unsigned long pages_to_scan;
	struct scan_rung *old_rung = slot->rung;

	/* leave the old rung it was in */
	if (list_empty(&slot->ksm_list)) {
		printk(KERN_ERR "KSM: Bug on vma %s\n", slot->vma->vm_mm->owner->comm);
		BUG();
	}

	if (old_rung->current_scan == &slot->ksm_list)
		old_rung->current_scan = slot->ksm_list.next;
	list_del_init(&slot->ksm_list);
	old_rung->vma_num--;
	if (slot->fully_scanned) {
		old_rung->fully_scanned_slots--;
	}

	if (old_rung->current_scan == &old_rung->vma_list) {
		/* This rung finishes a round */
		old_rung->round_finished = 1;
		old_rung->current_scan = old_rung->vma_list.next;
		BUG_ON(old_rung->current_scan == &old_rung->vma_list && !list_empty(&old_rung->vma_list));
	}

	/* enter the new rung */
	while (!(pages_to_scan =
		get_vma_random_scan_num(slot, rung->scan_ratio))) {
		rung++;
		BUG_ON(rung > &ksm_scan_ladder[ksm_scan_ladder_size -1]);
	}
	if (list_empty(&rung->vma_list))
		rung->current_scan = &slot->ksm_list;
	list_add(&slot->ksm_list, &rung->vma_list);
	slot->rung = rung;
	slot->pages_to_scan = pages_to_scan;
	//slot->pages_scanned = 0;
	slot->rung->vma_num++;
	if (slot->fully_scanned) {
		rung->fully_scanned_slots++;
	}




/*      buggy! if we do not hold the lock, vma may already exited.
	printk(KERN_ERR "KSM: %s enter ladder %d vma=%x dedup=%lu\n",
	       slot->vma->vm_mm->owner->comm, (rung - &ksm_scan_ladder[0]), (unsigned int)slot->vma, slot->dedup_ratio);
*/


	BUG_ON(rung->current_scan == &rung->vma_list && !list_empty(&rung->vma_list));

}

static inline void vma_rung_up(struct vma_slot *slot)
{
	if (slot->rung == &ksm_scan_ladder[ksm_scan_ladder_size-1])
		return;

	vma_rung_enter(slot, slot->rung + 1);
}

static inline void vma_rung_down(struct vma_slot *slot)
{
	if (slot->rung == &ksm_scan_ladder[0])
		return;

	vma_rung_enter(slot, slot->rung - 1);
}

/* can be refactored & beautified */
static unsigned long cal_dedup_ratio_clear(struct vma_slot *slot)
{
	int i;
	unsigned long dedup_num = 0, pages1 = slot->pages, scanned1;
	unsigned index;

	if (!slot->pages_scanned)
		return 0;

	//BUG_ON(slot->pages_scanned > pages1);
	scanned1 = slot->pages_scanned - slot->last_scanned;
	BUG_ON(scanned1 > slot->pages_scanned);
/*
	if (!scanned1) {
		printk(KERN_ERR "KSM: pages_scanned=%lu\n", slot->pages_scanned);
	}
*/

	for (i = 0; i < ksm_vma_table_index_end; i++) {
		struct vma_slot *slot2 = ksm_vma_table[i];
		unsigned long pages2, scanned2;

		if (!slot2 || i == slot->ksm_index || !slot2->pages_scanned)
			continue;

		pages2 = slot2->pages;

		//BUG_ON(vma2->pages_scanned > pages2);
		scanned2 = slot2->pages_scanned - slot2->last_scanned;
		//vma2->last_scanned = vma2->pages_scanned;
		BUG_ON(scanned2 > slot2->pages_scanned);

/*
		if (!scanned2) {
			printk(KERN_ERR "KSM: pages_scanned=%lu\n", vma2->pages_scanned);
		}
*/
		index = intertab_vma_offset(slot->ksm_index, i);
		BUG_ON(ksm_inter_vma_table[index] && (!scanned1 || !scanned2));
		if (ksm_inter_vma_table[index]) {
			dedup_num += ksm_inter_vma_table[index] * pages1 / scanned1
				     * pages2 / scanned2;
		}
		//ksm_inter_vma_table[index] = 0; /* Cleared data for this round */
	}

	index = intertab_vma_offset(slot->ksm_index, slot->ksm_index);
	BUG_ON(ksm_inter_vma_table[index] && !scanned1);
	if (ksm_inter_vma_table[index])
		dedup_num += ksm_inter_vma_table[index] * pages1 / scanned1;
	//ksm_inter_vma_table[index] = 0;

	return (dedup_num * KSM_SCAN_RATIO_MAX / pages1);
}

static inline void inc_current_sample_num(unsigned long delta)
{
	current_sample_num += 1 << delta;
	if (current_sample_num > HASH_STRENGTH_MAX)
		current_sample_num = HASH_STRENGTH_MAX;
	//printk(KERN_ERR "KSM: current_sample_num inc to %lu\n", current_sample_num);
}

static inline void dec_current_sample_num(unsigned long delta)
{
	unsigned long change = 1 << delta;

	if (current_sample_num <= change + 1)
		current_sample_num = 1;
	else
		current_sample_num -= change;

	//printk(KERN_ERR "KSM: current_sample_num dec to %lu\n", current_sample_num);
}

static inline void inc_sample_num_delta(void)
{
	sample_num_delta++;
	if (sample_num_delta > SAMPLE_NUM_DELTA_MAX)
		sample_num_delta = SAMPLE_NUM_DELTA_MAX;
}

static inline unsigned long get_current_neg_ratio(void)
{
	if (!rshash_pos || rshash_neg > rshash_pos)
		return 100;

	return div64_u64(100 * rshash_neg , rshash_pos);
}

static inline u64 get_current_benefit(void)
{
	if (rshash_neg > rshash_pos)
		return 0;

	return div64_u64((rshash_pos - rshash_neg), calsum_count);
}


static inline int judge_rshash_direction(void)
{
	u64 current_neg_ratio, stable_benefit;
	u64 current_benefit, delta = 0;

	current_neg_ratio = get_current_neg_ratio();

	if (rshash_neg == 0) {
		rshash_neg_cont_zero++;
		if (rshash_neg_cont_zero > 2) {

			return GO_DOWN;
		} else
			return STILL;
	} else
		rshash_neg_cont_zero = 0;

	if (current_neg_ratio > 90 ||
	    ksm_pages_round_collision * 100 > ksm_pages_round_scanned * 5 )
		return GO_UP;

	current_benefit = get_current_benefit();
	stable_benefit = rshash_state.stable_benefit;

	if (!stable_benefit)
		goto out1;

	if (current_benefit > stable_benefit)
		delta = current_benefit - stable_benefit;
	else if (current_benefit < stable_benefit)
		delta = stable_benefit - current_benefit;

	delta = div64_u64(100 * delta , stable_benefit);

	if (delta > 50) {
out1:
		return OBSCURE;
	}

	return STILL;
}

static inline void stable_node_reinsert(struct stable_node *new_node,
					struct page *page,
					struct rb_root *root_treep,
					struct list_head *tree_node_listp,
					u32 checksum_val)
{
	struct rb_node **new = &root_treep->rb_node;
	struct rb_node *parent = NULL;
	struct stable_node *stable_node;
	struct tree_node *rnode;
	struct page *tree_page;
	int cmp;

	while (*new) {
		//struct rmap_item *tree_rmap_item;
		//
		int cmp;

		rnode = rb_entry(*new, struct tree_node, node);

		cmp = checksum_cmp(checksum_val, rnode->checksum_val);

		if (cmp < 0) {
			parent = *new;
			new = &parent->rb_left;
		} else if (cmp > 0) {
			parent = *new;
			new = &parent->rb_right;
		} else
			break;
	}

	if (*new) {
		/* find a stable tree node with same first level hash value */
		stable_node_full_hash(new_node, page, checksum_val);
		if (rnode->count == 1) {
			stable_node = rb_entry(rnode->sub_root.rb_node,
					       struct stable_node, node);
			tree_page = get_ksm_page(stable_node, 0);
			if (tree_page) {
				stable_node_full_hash(stable_node,
						      tree_page, checksum_val);
				put_page(tree_page);

				/* prepare for stable node insertion */

				cmp = checksum_cmp(new_node->checksum_full,
						   stable_node->checksum_full);
				parent = &stable_node->node;
				if (cmp < 0) {
					new = &parent->rb_left;
				} else if (cmp > 0) {
					new = &parent->rb_right;
				} else
					goto failed;

				goto add_node;
			} else {
				/* the only stable_node deleted, the tree node
				 * was also deleted.
				 */
				goto tree_node_reuse;
			}
		}

		/* well, search the collision subtree */
		new = &rnode->sub_root.rb_node;
		parent = NULL;
		BUG_ON(!*new);
		while (*new) {
			int cmp;

			stable_node = rb_entry(*new, struct stable_node, node);

			cmp = checksum_cmp(new_node->checksum_full,
					   stable_node->checksum_full);

			if (cmp < 0) {
				parent = *new;
				new = &parent->rb_left;
			} else if (cmp > 0) {
				parent = *new;
				new = &parent->rb_right;
			} else {
				/* oh, no, still a collision */
				goto failed;
			}
		}

		goto add_node;
	}

	/* no tree node found */
	rnode = alloc_tree_node(tree_node_listp);
	if (!rnode) {
		printk(KERN_ERR "KSM: memory allocation error!\n");
		goto failed;
	} else {
		rnode->checksum_val = checksum_val;
		rb_link_node(&rnode->node, parent, new);
		rb_insert_color(&rnode->node, root_treep);

tree_node_reuse:
		/* prepare for stable node insertion */
		parent = NULL;
		new = &rnode->sub_root.rb_node;
	}

add_node:
	rb_link_node(&new_node->node, parent, new);
	rb_insert_color(&new_node->node, &rnode->sub_root);
	new_node->tree_node = rnode;
	rnode->count++;
	return;

failed:
	/* This can only happen when two nodes have collided
	 * in two levels.
	 */
	new_node->tree_node = NULL;
//	list_add(&new_node->hell_node, &stable_node_hell);
	return;
}

static inline void free_all_tree_nodes(struct list_head *list)
{
	struct tree_node *node, *tmp;

	list_for_each_entry_safe(node, tmp, list, all_list) {
		free_tree_node(node);
	}
}

static inline void stable_tree_delta_hash(u32 prev_sample_num)
{
	struct stable_node *node, *tmp;
	struct rb_root *root_new_treep;
	struct list_head *new_tree_node_listp;

	stable_tree_index = (stable_tree_index + 1) % 2;
	root_new_treep = &root_stable_tree[stable_tree_index];
	new_tree_node_listp = &stable_tree_node_list[stable_tree_index];
	*root_new_treep = RB_ROOT;
	BUG_ON(!list_empty(new_tree_node_listp));
	//INIT_LIST_HEAD(&stable_node_hell);
	/* we need to be safe, the node could be removed by get_ksm_page()
	 * or by stable_node_reinsert() to hell list.
	 */
	list_for_each_entry_safe(node, tmp, &stable_node_list, all_list) {
		void *addr;
		struct page *node_page;
		u32 checksum_val;

		//node->status = STAT_NONE;
		/* init the rbnode and collision list,
		 * because it would be removed.
		 */
		node_page = get_ksm_page(node, 0);
		if (!node_page)
			continue;

		addr = kmap_atomic(node_page, KM_USER0);

		checksum_val = delta_hash(addr, prev_sample_num,
					  current_sample_num,
					  node->tree_node->checksum_val);
		kunmap_atomic(addr, KM_USER0);
		stable_node_reinsert(node, node_page, root_new_treep,
				     new_tree_node_listp, checksum_val);
		put_page(node_page);
	}

	root_stable_treep = root_new_treep;
	free_all_tree_nodes(stable_tree_node_listp);
	BUG_ON(!list_empty(stable_tree_node_listp));
	stable_tree_node_listp = new_tree_node_listp;
}

static inline void rshash_adjust(void)
{
	unsigned long prev_sample_num = current_sample_num;

	if (!calsum_count)
		return;

/*
	printk(KERN_ERR "KSM: rshash_neg=%lu  rshash_pos=%lu benefit=%lu\n",
	       rshash_neg, rshash_pos, get_current_benefit());
*/


	if (rshash_neg >= rshash_pos &&
	    rshash_state.state == RSHASH_NEW) {
		inc_current_sample_num(sample_num_delta);
		inc_sample_num_delta();
		goto out;
	}

	if (rshash_neg == 0 &&
	    rshash_state.state == RSHASH_NEW) {
		dec_current_sample_num(sample_num_delta);
		inc_sample_num_delta();
		goto out;
	}



	switch (rshash_state.state) {
	case RSHASH_STILL:
		//printk(KERN_ERR "KSM: enter state STILL\n");
		switch (judge_rshash_direction()) {
		case GO_UP:
			if (rshash_state.pre_direct == GO_DOWN)
				sample_num_delta = 0;

			inc_current_sample_num(sample_num_delta);
			inc_sample_num_delta();
			rshash_state.stable_benefit = get_current_benefit();
			rshash_state.pre_direct = GO_UP;
			break;

		case GO_DOWN:
			if (rshash_state.pre_direct == GO_UP)
				sample_num_delta = 0;

			dec_current_sample_num(sample_num_delta);
			inc_sample_num_delta();
			rshash_state.stable_benefit = get_current_benefit();
			rshash_state.pre_direct = GO_DOWN;
			break;

		case OBSCURE:
			rshash_state.stable_point = current_sample_num;
			rshash_state.turn_point_down = current_sample_num;
			rshash_state.turn_point_up = current_sample_num;
			rshash_state.turn_benefit_down = get_current_benefit();
			rshash_state.turn_benefit_up = get_current_benefit();
			rshash_state.lookup_window_index = 0;
			rshash_state.state = RSHASH_TRYDOWN;
			dec_current_sample_num(sample_num_delta);
			inc_sample_num_delta();

			break;

		case STILL:
			break;
		default:
			BUG();
		}
		break;

	case RSHASH_TRYDOWN:
		//printk(KERN_ERR "KSM: enter state TRYDOWN\n");
		if (rshash_state.lookup_window_index++ % 5 == 0)
			rshash_state.below_count = 0;

		if (get_current_benefit() < rshash_state.stable_benefit)
			rshash_state.below_count++;
		else if (get_current_benefit() > rshash_state.turn_benefit_down) {
			rshash_state.turn_point_down = current_sample_num;
			rshash_state.turn_benefit_down = get_current_benefit();
		}

		if (rshash_state.below_count >= 3 ||
		    judge_rshash_direction() == GO_UP) {
			current_sample_num = rshash_state.stable_point;
			sample_num_delta = 0;
			inc_current_sample_num(sample_num_delta);
			inc_sample_num_delta();
			rshash_state.lookup_window_index = 0;
			rshash_state.state = RSHASH_TRYUP;
			sample_num_delta = 0;
/*
			printk(KERN_ERR "KSM: finished state TRYDOWN with turn_point=%lu benefit=%lu\n",
			       rshash_state.turn_point_down, rshash_state.turn_benefit_down);
*/
		} else {
			dec_current_sample_num(sample_num_delta);
			inc_sample_num_delta();
		}
		break;

	case RSHASH_TRYUP:
		//printk(KERN_ERR "KSM: enter state TRYUP\n");
		if (rshash_state.lookup_window_index++ % 5 == 0)
			rshash_state.below_count = 0;

		if (get_current_benefit() < rshash_state.stable_benefit)
			rshash_state.below_count++;
		else if (get_current_benefit() > rshash_state.turn_benefit_up) {
			rshash_state.turn_point_up = current_sample_num;
			rshash_state.turn_benefit_up = get_current_benefit();
		}

		if (rshash_state.below_count >= 3 ||
		    judge_rshash_direction() == GO_DOWN) {
			current_sample_num = rshash_state.turn_benefit_up >
			rshash_state.turn_benefit_down ? rshash_state.turn_point_up :
			rshash_state.turn_point_down;
			rshash_state.state = RSHASH_PRE_STILL;
/*
			printk(KERN_ERR "KSM: finished state TRYUP with turn_point=%lu benefit=%lu current_sample_num=%lu\n",
			       rshash_state.turn_point_up, rshash_state.turn_benefit_up, current_sample_num);
*/

		} else {
			inc_current_sample_num(sample_num_delta);
			inc_sample_num_delta();
		}

		break;

	case RSHASH_NEW:
		//printk(KERN_ERR "KSM: enter state NEW\n");
	case RSHASH_PRE_STILL:
		//printk(KERN_ERR "KSM: enter state PRE_STILL\n");
		rshash_state.stable_benefit = get_current_benefit();
		rshash_state.state = RSHASH_STILL;
		sample_num_delta = 0;
		break;
	default:
		BUG();
	}

out:
	rshash_neg = rshash_pos = calsum_count = 0;

	if (prev_sample_num != current_sample_num) {
		printk(KERN_ERR "KSM: rehash stable tree\n");
		stable_tree_delta_hash(prev_sample_num);
	}
}

static void round_update_ladder(void)
{
	int i;
	struct vma_slot *slot, *tmp_slot;
	unsigned long dedup_ratio_max = 0, dedup_ratio_mean = 0;
	unsigned long threshold;
	struct list_head tmp_list;

	for (i = 0; i < ksm_vma_table_index_end; i++) {
		if ((slot = ksm_vma_table[i])) {
			slot->dedup_ratio = cal_dedup_ratio_clear(slot);
			if (dedup_ratio_max < slot->dedup_ratio)
				dedup_ratio_max = slot->dedup_ratio;
			dedup_ratio_mean += slot->dedup_ratio;
		}
	}

	dedup_ratio_mean /= ksm_vma_slot_num;
	threshold = dedup_ratio_mean;

	for (i = 0; i < ksm_vma_table_index_end; i++) {
		if ((slot = ksm_vma_table[i])) {
			if (slot->dedup_ratio  &&
			    slot->dedup_ratio >= threshold) {
				vma_rung_up(slot);
			} else {
				vma_rung_down(slot);
			}

			ksm_intertab_clear(slot);
			ksm_vma_table_num--;
			ksm_vma_table[i] = NULL;
			slot->ksm_index = -1;
			slot->slot_scanned = 0;
			slot->dedup_ratio = 0;
		}
	}

	INIT_LIST_HEAD(&tmp_list);
	for (i = 0; i < ksm_scan_ladder_size; i++) {
		list_for_each_entry_safe(slot, tmp_slot, &ksm_scan_ladder[i].vma_list,
					 ksm_list) {
			/**
			 * The slots were scanned but not in inter_tab, their dedup must
			 * be 0.
			 */
			if (slot->slot_scanned) {
				BUG_ON(slot->dedup_ratio != 0);
				vma_rung_down(slot);
				//list_del(&slot->ksm_list);
				//list_add(&slot->ksm_list, &tmp_list);
			}

			slot->dedup_ratio = 0;
		}
	}

/*
	list_for_each_entry(tmp_slot, &tmp_list, ksm_list) {
		vma_rung_down(tmp_slot);
	}
*/


	BUG_ON(ksm_vma_table_num != 0);
	ksm_vma_table_index_end = 0;

	for (i = 0; i < ksm_scan_ladder_size; i++) {
		ksm_scan_ladder[i].round_finished = 0;
		//ksm_scan_ladder[i].fully_scanned_slots = 0;
		ksm_scan_ladder[i].scan_turn = 1;

		list_for_each_entry(slot, &ksm_scan_ladder[i].vma_list,
				    ksm_list) {
			//slot->pages_scanned = 0;
			slot->last_scanned = slot->pages_scanned;
			slot->slot_scanned = 0;
			if (slot->fully_scanned) {
				slot->fully_scanned = 0;
				ksm_scan_ladder[i].fully_scanned_slots--;
			}
			BUG_ON(slot->ksm_index != -1);
        	}

		BUG_ON(ksm_scan_ladder[i].fully_scanned_slots);
		//ksm_scan_ladder[i].vma_finished = 0;
	}

	rshash_adjust();

	ksm_pages_scanned += ksm_pages_round_scanned;
	ksm_pages_round_scanned = 0;
	ksm_pages_round_collision = 0;
}

static inline unsigned int ksm_pages_to_scan(unsigned int batch_pages)
{
	return totalram_pages * batch_pages / 1000000;
}

static void inline cal_ladder_pages_to_scan(unsigned int num)
{
	int i;

	for (i = 0; i < ksm_scan_ladder_size; i++) {
		ksm_scan_ladder[i].pages_to_scan = num
			* ksm_scan_ladder[i].scan_ratio / KSM_SCAN_RATIO_MAX;
	}
}


/**
 * ksm_do_scan  - the ksm scanner main worker function.
 * @scan_npages - number of pages we want to scan before we return.
 */
static void ksm_do_scan(void)
{
	struct vma_slot *slot, *iter;
	struct list_head *next_scan, *iter_head;
	struct mm_struct *busy_mm;
	unsigned char round_finished = 1, all_rungs_emtpy;
	int i, err;
	unsigned long rest_pages = 0;

	might_sleep();

	for (i = ksm_scan_ladder_size - 1; i >= 0; i--) {
		struct scan_rung *rung = &ksm_scan_ladder[i];

		if (list_empty(&rung->vma_list))
			continue;

		if (rung->fully_scanned_slots == rung->vma_num && !rung->fully_scanned_slots) {
			rest_pages += rung->pages_to_scan;
			continue;
		}

		rung->pages_to_scan += rest_pages;
		rest_pages = 0;
		while (rung->pages_to_scan) {
//			int vma_busy = 0, n = 1;
cleanup:
			cleanup_vma_slots();

			if (list_empty(&rung->vma_list))
				break;

rescan:
			BUG_ON(rung->current_scan == &rung->vma_list && !list_empty(&rung->vma_list));
			slot = list_entry(rung->current_scan,
					 struct vma_slot, ksm_list);

			err = down_read_slot_mmap_sem(slot);
			if (err == -ENOENT)
				goto cleanup;

			busy_mm = slot->mm;

busy:
			if (err == -EBUSY) {
				/* skip other vmas on the same mm */
				iter = slot;
				iter_head = slot->ksm_list.next;

				/**
				 * Since we did not hold vma_slot_list_lock during the loop,
				 * There is rare possiblity that can skip a good slot.
				 * No locking until we are sure that it causes problems.
				 */
				while(iter_head != &rung->vma_list) {
					iter = list_entry(iter_head,
							  struct vma_slot,
							  ksm_list);
					if (iter->vma->vm_mm != busy_mm)
						break;
					iter_head = iter_head->next;
				}

				if (iter->vma->vm_mm != busy_mm) {
					rung->current_scan = &iter->ksm_list;
					BUG_ON(rung->current_scan == &rung->vma_list && !list_empty(&rung->vma_list));
					//printk(KERN_ERR "KSM: skip to next mm !\n");
					goto rescan;
				} else {/* This is the only vma on this rung */
					//printk(KERN_ERR "KSM: skip to next rung !\n");
					break;
				}
			}

			BUG_ON(!vma_can_enter(slot->vma));
			if (ksm_test_exit(slot->vma->vm_mm)) {
				busy_mm = slot->vma->vm_mm;
				up_read(&slot->vma->vm_mm->mmap_sem);
				err = -EBUSY;
				goto busy;
			}


			/* Ok, we have take the mmap_sem, ready to scan */
			if (!slot->fully_scanned)
				scan_vma_one_page(slot);
			up_read(&slot->vma->vm_mm->mmap_sem);

			//BUG_ON(slot->pages_scanned > vma_pages(vma));
			if ((slot->pages_scanned &&
			     slot->pages_scanned % slot->pages_to_scan == 0)
			    || slot->fully_scanned) {
				//slot->pages_scanned = 0;
				next_scan = rung->current_scan->next;
				if (next_scan == &rung->vma_list) {
					/* This rung finishes a rung scan turn */
					rung->round_finished = 1;
					rung->scan_turn++;
					BUG_ON(!rung->scan_turn);
					rung->current_scan = rung->vma_list.next;
					BUG_ON(rung->current_scan == &rung->vma_list && !list_empty(&rung->vma_list));
					if (rung->vma_num == rung->fully_scanned_slots) {
						rest_pages += rung->pages_to_scan;
						break;
						//printk(KERN_ERR "KSM: solo round finished !\n");
						//goto pre_next_round;
					}
				} else {
					rung->current_scan = next_scan;
					BUG_ON(rung->current_scan == &rung->vma_list && !list_empty(&rung->vma_list));
				}
			}

			cond_resched();
		}
	}

	all_rungs_emtpy = 1;
	for (i = 0; i < ksm_scan_ladder_size; i++) {
		struct scan_rung *rung = &ksm_scan_ladder[i];

		if (!list_empty(&rung->vma_list)) {
			all_rungs_emtpy = 0;
			if (!rung->round_finished)
				round_finished = 0;
			break;
		}
	}

	if (all_rungs_emtpy)
		round_finished = 0;

	cleanup_vma_slots();

//pre_next_round:
	if (round_finished) {
		//printk(KERN_ERR "KSM: round finished !\n");
		round_update_ladder();

		/* sync with ksm_remove_vma for rb_erase */
		ksm_scan_round++;
		root_unstable_tree = RB_ROOT;
		free_all_tree_nodes(&unstable_tree_node_list);
	}
	cal_ladder_pages_to_scan(ksm_scan_batch_pages);
}

static int ksmd_should_run(void)
{
	return (ksm_run & KSM_RUN_MERGE);
}

static inline unsigned int ksm_mips_time_to_jiffies(unsigned int mips_time)
{
	return mips_time * 500000  / loops_per_jiffy;
}

/**
 *
 *
 *
 * @param slot
 *
 * @return int , 1 on success, 0 on failure
 */
static int ksm_vma_enter(struct vma_slot *slot)
{
	struct scan_rung *rung;
	unsigned long pages_to_scan, pool_size;

	while (slot->pages != vma_pages(slot->vma)) spin_lock(&vma_slot_list_lock);
	rung = &ksm_scan_ladder[0];
	if ((pages_to_scan = get_vma_random_scan_num(slot, rung->scan_ratio))) {
		if (list_empty(&rung->vma_list))
			rung->current_scan = &slot->ksm_list;
		if (!list_empty(&slot->ksm_list)) {
			printk(KERN_ERR "BUG:KSM slot->ksm_list should be emtpy process:%s\n", slot->vma->vm_mm->owner->comm);
		}
		list_add(&slot->ksm_list, &rung->vma_list);
		slot->rung = rung;
		slot->pages_to_scan = pages_to_scan;
		slot->rung->vma_num++;
		//vma->vm_flags |= VM_MERGEABLE;
		BUG_ON(PAGE_SIZE % sizeof(struct rmap_list_entry) != 0);

		pool_size = vma_pool_size(slot->vma);

		slot->rmap_list_pool = kzalloc(sizeof(struct page*) * pool_size, GFP_NOWAIT);
		slot->pool_counts = kzalloc(sizeof(unsigned long) * pool_size, GFP_NOWAIT);
		slot->pool_size = pool_size;
		BUG_ON(!slot->rmap_list_pool);
		BUG_ON(!slot->pool_counts);


/*
		printk(KERN_ERR "KSM: added task=%s vma=%x\n",
		       slot->vma->vm_mm->owner->comm, (unsigned int)slot->vma);
*/

		BUG_ON(rung->current_scan == &rung->vma_list && !list_empty(&rung->vma_list));

		ksm_vma_slot_num++;
		BUG_ON(!ksm_vma_slot_num);
		return 1;

	}

	return 0;
}


static void ksm_enter_all_slots(void)
{
	struct vma_slot *slot;
	int added;

	spin_lock(&vma_slot_list_lock);
	while (!list_empty(&vma_slot_new)) {
		slot = list_entry(vma_slot_new.next, struct vma_slot, slot_list);

//		if (time_before(jiffies, slot->ctime_j + msecs_to_jiffies(1000))) {
			/**
			 * slots are sorted by ctime_j, if one found to be too
			 * young, just stop scanning the rest ones.
			 */
			//printk(KERN_ERR "KSM: skip too young vma=%x\n", slot->vma);
//			spin_unlock(&vma_slot_list_lock);
//			return;
//		}

		list_del_init(&slot->slot_list);
		added = 0;
		if (vma_can_enter(slot->vma))
			added = ksm_vma_enter(slot);

		if (!added) {
			/* Put back to new list to be del by its creator process */
			slot->ctime_j = jiffies;
			list_del(&slot->slot_list);
			list_add_tail(&slot->slot_list, &vma_slot_noadd);
		}
		spin_unlock(&vma_slot_list_lock);
		cond_resched();
		spin_lock(&vma_slot_list_lock);
	}
	spin_unlock(&vma_slot_list_lock);
}

static int ksm_scan_thread(void *nothing)
{
	set_user_nice(current, 5);

	while (!kthread_should_stop()) {
		mutex_lock(&ksm_thread_mutex);
		if (ksmd_should_run()) {
			if (!slots_enter_last ||
			    time_after(jiffies, slots_enter_last +
				       msecs_to_jiffies(slots_enter_interval))) {
				ksm_enter_all_slots();
				slots_enter_last = jiffies;
			}
			ksm_do_scan();
		}
		mutex_unlock(&ksm_thread_mutex);

		if (ksmd_should_run()) {
			schedule_timeout_interruptible(ksm_thread_sleep_jiffies);
			ksm_sleep_times++;
		} else {
			wait_event_interruptible(ksm_thread_wait,
				ksmd_should_run() || kthread_should_stop());
		}
	}
	return 0;
}

struct page *ksm_does_need_to_copy(struct page *page,
			struct vm_area_struct *vma, unsigned long address)
{
	struct page *new_page;

	unlock_page(page);	/* any racers will COW it, not modify it */

	new_page = alloc_page_vma(GFP_HIGHUSER_MOVABLE, vma, address);
	if (new_page) {
		copy_user_highpage(new_page, page, address, vma);

		SetPageDirty(new_page);
		__SetPageUptodate(new_page);
		SetPageSwapBacked(new_page);
		__set_page_locked(new_page);

		if (page_evictable(new_page, vma))
			lru_cache_add_lru(new_page, LRU_ACTIVE_ANON);
		else
			add_page_to_unevictable_list(new_page);
	}

	page_cache_release(page);
	return new_page;
}

int page_referenced_ksm(struct page *page, struct mem_cgroup *memcg,
			unsigned long *vm_flags)
{
	struct stable_node *stable_node;
	struct node_vma *node_vma;
	struct rmap_item *rmap_item;
	struct hlist_node *hlist, *rmap_hlist;
	unsigned int mapcount = page_mapcount(page);
	int referenced = 0;
	int search_new_forks = 0;

	VM_BUG_ON(!PageKsm(page));
	VM_BUG_ON(!PageLocked(page));

	stable_node = page_stable_node(page);
	if (!stable_node)
		return 0;


again:
	hlist_for_each_entry(node_vma, hlist, &stable_node->hlist, hlist) {
		hlist_for_each_entry(rmap_item, rmap_hlist,
				     &node_vma->rmap_hlist, hlist) {
			struct anon_vma *anon_vma = rmap_item->anon_vma;
			struct vm_area_struct *vma;

			spin_lock(&anon_vma->lock);
			list_for_each_entry(vma, &anon_vma->head,
					    anon_vma_node) {
				unsigned long address = get_rmap_addr(rmap_item);

				if (address < vma->vm_start ||
				    address >= vma->vm_end)
					continue;
				/*
				 * Initially we examine only the vma which
				 * covers this rmap_item; but later, if there
				 * is still work to do, we examine covering
				 * vmas in other mms: in case they were forked
				 * from the original since ksmd passed.
				 */
				if ((rmap_item->slot->vma == vma) == search_new_forks)
					continue;

				if (memcg && !mm_match_cgroup(vma->vm_mm, memcg))
					continue;

				referenced +=
					page_referenced_one(page, vma, address,
							    &mapcount, vm_flags);
				if (!search_new_forks || !mapcount)
					break;
			}
			spin_unlock(&anon_vma->lock);
			if (!mapcount)
				goto out;
		}
	}
	if (!search_new_forks++)
		goto again;
out:
	return referenced;
}

int try_to_unmap_ksm(struct page *page, enum ttu_flags flags)
{
	struct stable_node *stable_node;
	struct node_vma *node_vma;
	struct hlist_node *hlist, *rmap_hlist;
	struct rmap_item *rmap_item;
	int ret = SWAP_AGAIN;
	int search_new_forks = 0;

	VM_BUG_ON(!PageKsm(page));
	VM_BUG_ON(!PageLocked(page));

	stable_node = page_stable_node(page);
	if (!stable_node)
		return SWAP_FAIL;
again:
	hlist_for_each_entry(node_vma, hlist, &stable_node->hlist, hlist) {
		hlist_for_each_entry(rmap_item, rmap_hlist,
				     &node_vma->rmap_hlist, hlist) {
			struct anon_vma *anon_vma = rmap_item->anon_vma;
			struct vm_area_struct *vma;

			spin_lock(&anon_vma->lock);
			list_for_each_entry(vma, &anon_vma->head,
					    anon_vma_node) {
				unsigned long address = get_rmap_addr(rmap_item);

				if (address < vma->vm_start ||
				    address >= vma->vm_end)
					continue;
				/*
				 * Initially we examine only the vma which covers this
				 * rmap_item; but later, if there is still work to do,
				 * we examine covering vmas in other mms: in case they
				 * were forked from the original since ksmd passed.
				 */
				if ((rmap_item->slot->vma == vma) == search_new_forks)
					continue;

				ret = try_to_unmap_one(page, vma, address, flags);
				if (ret != SWAP_AGAIN || !page_mapped(page)) {
					spin_unlock(&anon_vma->lock);
					goto out;
				}
			}
			spin_unlock(&anon_vma->lock);
		}
	}
	if (!search_new_forks++)
		goto again;
out:
	return ret;
}

#ifdef CONFIG_MIGRATION
int rmap_walk_ksm(struct page *page, int (*rmap_one)(struct page *,
		  struct vm_area_struct *, unsigned long, void *), void *arg)
{
	struct stable_node *stable_node;
	struct node_vma *node_vma;
	struct hlist_node *hlist, *rmap_hlist;
	struct rmap_item *rmap_item;
	int ret = SWAP_AGAIN;
	int search_new_forks = 0;

	VM_BUG_ON(!PageKsm(page));
	VM_BUG_ON(!PageLocked(page));

	stable_node = page_stable_node(page);
	if (!stable_node)
		return ret;
again:
	hlist_for_each_entry(node_vma, hlist, &stable_node->hlist, hlist) {
		hlist_for_each_entry(rmap_item, rmap_hlist,
				     &node_vma->rmap_hlist, hlist) {
			struct anon_vma *anon_vma = rmap_item->anon_vma;
			struct vm_area_struct *vma;

			spin_lock(&anon_vma->lock);
			list_for_each_entry(vma, &anon_vma->head, anon_vma_node) {
				unsigned long address = get_rmap_addr(rmap_item);

				if (address < vma->vm_start ||
				    address >= vma->vm_end)
					continue;
				/*
				 * Initially we examine only the vma which covers this
				 * rmap_item; but later, if there is still work to do,
				 * we examine covering vmas in other mms: in case they
				 * were forked from the original since ksmd passed.
				 */
				if ((rmap_item->slot->vma == vma) == search_new_forks)
					continue;

				ret = rmap_one(page, vma, address, arg);
				if (ret != SWAP_AGAIN) {
					spin_unlock(&anon_vma->lock);
					goto out;
				}
			}
			spin_unlock(&anon_vma->lock);
		}
	}
	if (!search_new_forks++)
		goto again;
out:
	return ret;
}

void ksm_migrate_page(struct page *newpage, struct page *oldpage)
{
	struct stable_node *stable_node;

	VM_BUG_ON(!PageLocked(oldpage));
	VM_BUG_ON(!PageLocked(newpage));
	VM_BUG_ON(newpage->mapping != oldpage->mapping);

	stable_node = page_stable_node(newpage);
	if (stable_node) {
		VM_BUG_ON(stable_node->kpfn != page_to_pfn(oldpage));
		stable_node->kpfn = page_to_pfn(newpage);
	}
}
#endif /* CONFIG_MIGRATION */

#ifdef CONFIG_MEMORY_HOTREMOVE
static struct stable_node *ksm_check_stable_tree(unsigned long start_pfn,
						 unsigned long end_pfn)
{
	struct rb_node *node;

	for (node = rb_first(root_stable_treep); node; node = rb_next(node)) {
		struct stable_node *stable_node;

		stable_node = rb_entry(node, struct stable_node, node);
		if (stable_node->kpfn >= start_pfn &&
		    stable_node->kpfn < end_pfn)
			return stable_node;
	}
	return NULL;
}

static int ksm_memory_callback(struct notifier_block *self,
			       unsigned long action, void *arg)
{
	struct memory_notify *mn = arg;
	struct stable_node *stable_node;

	switch (action) {
	case MEM_GOING_OFFLINE:
		/*
		 * Keep it very simple for now: just lock out ksmd and
		 * MADV_UNMERGEABLE while any memory is going offline.
		 */
		mutex_lock(&ksm_thread_mutex);
		break;

	case MEM_OFFLINE:
		/*
		 * Most of the work is done by page migration; but there might
		 * be a few stable_nodes left over, still pointing to struct
		 * pages which have been offlined: prune those from the tree.
		 */
		while ((stable_node = ksm_check_stable_tree(mn->start_pfn,
					mn->start_pfn + mn->nr_pages)) != NULL)
			remove_node_from_stable_tree(stable_node, 1);
		/* fallthrough */

	case MEM_CANCEL_OFFLINE:
		mutex_unlock(&ksm_thread_mutex);
		break;
	}
	return NOTIFY_OK;
}
#endif /* CONFIG_MEMORY_HOTREMOVE */

#ifdef CONFIG_SYSFS
/*
 * This all compiles without CONFIG_SYSFS, but is a waste of space.
 */

#define KSM_ATTR_RO(_name) \
	static struct kobj_attribute _name##_attr = __ATTR_RO(_name)
#define KSM_ATTR(_name) \
	static struct kobj_attribute _name##_attr = \
		__ATTR(_name, 0644, _name##_show, _name##_store)

static ssize_t sleep_millisecs_show(struct kobject *kobj,
				    struct kobj_attribute *attr, char *buf)
{
	return sprintf(buf, "%u\n", jiffies_to_msecs(ksm_thread_sleep_jiffies));
}

static ssize_t sleep_millisecs_store(struct kobject *kobj,
				     struct kobj_attribute *attr,
				     const char *buf, size_t count)
{
	unsigned long msecs;
	int err;

	err = strict_strtoul(buf, 10, &msecs);
	if (err || msecs > UINT_MAX)
		return -EINVAL;

	ksm_thread_sleep_jiffies = msecs_to_jiffies(msecs);
	printk(KERN_INFO "KSM: sleep interval changed to %u jiffies\n",
	       ksm_thread_sleep_jiffies);


	return count;
}
KSM_ATTR(sleep_millisecs);

//-------------------------------------------------------
static ssize_t min_scan_ratio_show(struct kobject *kobj,
				    struct kobj_attribute *attr, char *buf)
{
	return sprintf(buf, "%u\n", ksm_min_scan_ratio);
}

static ssize_t min_scan_ratio_store(struct kobject *kobj,
				     struct kobj_attribute *attr,
				     const char *buf, size_t count)
{
	unsigned long msr;
	int err;

	err = strict_strtoul(buf, 10, &msr);
	if (err || msr > UINT_MAX)
		return -EINVAL;

	ksm_min_scan_ratio = msr;

	return count;
}
KSM_ATTR(min_scan_ratio);

//-------------------------------------------------------


static ssize_t scan_batch_pages_show(struct kobject *kobj,
				  struct kobj_attribute *attr, char *buf)
{
	return sprintf(buf, "%lu\n", ksm_scan_batch_pages);
}

static ssize_t scan_batch_pages_store(struct kobject *kobj,
				   struct kobj_attribute *attr,
				   const char *buf, size_t count)
{
	int err;
	unsigned long batch_pages;

	err = strict_strtoul(buf, 10, &batch_pages);
	if (err || batch_pages > UINT_MAX)
		return -EINVAL;

	ksm_scan_batch_pages = batch_pages;
	cal_ladder_pages_to_scan(ksm_scan_batch_pages);

	return count;
}
KSM_ATTR(scan_batch_pages);

static ssize_t run_show(struct kobject *kobj, struct kobj_attribute *attr,
			char *buf)
{
	return sprintf(buf, "%u\n", ksm_run);
}

static ssize_t run_store(struct kobject *kobj, struct kobj_attribute *attr,
			 const char *buf, size_t count)
{
	int err;
	unsigned long flags;

	err = strict_strtoul(buf, 10, &flags);
	if (err || flags > UINT_MAX)
		return -EINVAL;
	if (flags > KSM_RUN_MERGE)
		return -EINVAL;

	/*
	 * KSM_RUN_MERGE sets ksmd running, and 0 stops it running.
	 * KSM_RUN_UNMERGE stops it running and unmerges all rmap_items,
	 * breaking COW to free the pages_shared (but leaves mm_slots
	 * on the list for when ksmd may be set running again).
	 */

	mutex_lock(&ksm_thread_mutex);
	if (ksm_run != flags) {
		ksm_run = flags;
	}
	mutex_unlock(&ksm_thread_mutex);

	if (flags & KSM_RUN_MERGE)
		wake_up_interruptible(&ksm_thread_wait);

	return count;
}
KSM_ATTR(run);

static ssize_t pages_shared_show(struct kobject *kobj,
				 struct kobj_attribute *attr, char *buf)
{
	return sprintf(buf, "%lu\n", ksm_pages_shared);
}
KSM_ATTR_RO(pages_shared);

static ssize_t pages_sharing_show(struct kobject *kobj,
				  struct kobj_attribute *attr, char *buf)
{
	return sprintf(buf, "%lu\n", ksm_pages_sharing);
}
KSM_ATTR_RO(pages_sharing);

static ssize_t pages_unshared_show(struct kobject *kobj,
				   struct kobj_attribute *attr, char *buf)
{
	return sprintf(buf, "%lu\n", ksm_pages_unshared);
}
KSM_ATTR_RO(pages_unshared);

static ssize_t pages_volatile_show(struct kobject *kobj,
				   struct kobj_attribute *attr, char *buf)
{
	long ksm_pages_volatile;

	ksm_pages_volatile = ksm_rmap_items - ksm_pages_shared
				- ksm_pages_sharing - ksm_pages_unshared;
	/*
	 * It was not worth any locking to calculate that statistic,
	 * but it might therefore sometimes be negative: conceal that.
	 */
	if (ksm_pages_volatile < 0)
		ksm_pages_volatile = 0;
	return sprintf(buf, "%ld\n", ksm_pages_volatile);
}
KSM_ATTR_RO(pages_volatile);

static ssize_t full_scans_show(struct kobject *kobj,
			       struct kobj_attribute *attr, char *buf)
{
	return sprintf(buf, "%llu\n", ksm_scan_round);
}
KSM_ATTR_RO(full_scans);

static ssize_t pages_scanned_show(struct kobject *kobj,
                                 struct kobj_attribute *attr, char *buf)
{
       return sprintf(buf, "%llu\n", ksm_pages_scanned);
}
KSM_ATTR_RO(pages_scanned);

static ssize_t current_sample_num_show(struct kobject *kobj,
				  struct kobj_attribute *attr, char *buf)
{
	return sprintf(buf, "%lu\n", current_sample_num);
}
KSM_ATTR_RO(current_sample_num);

static ssize_t sleep_times_show(struct kobject *kobj,
				  struct kobj_attribute *attr, char *buf)
{
	return sprintf(buf, "%llu\n", ksm_sleep_times);
}
KSM_ATTR_RO(sleep_times);


static struct attribute *ksm_attrs[] = {
	&sleep_millisecs_attr.attr,
	&scan_batch_pages_attr.attr,
	&run_attr.attr,
	&pages_shared_attr.attr,
	&pages_sharing_attr.attr,
	&pages_unshared_attr.attr,
	&pages_volatile_attr.attr,
	&full_scans_attr.attr,
	&min_scan_ratio_attr.attr,
	&pages_scanned_attr.attr,
	&current_sample_num_attr.attr,
	&sleep_times_attr.attr,
	NULL,
};

static struct attribute_group ksm_attr_group = {
	.attrs = ksm_attrs,
	.name = "ksm",
};
#endif /* CONFIG_SYSFS */

static void inline init_scan_ladder(void)
{
	int i;
	unsigned long mul = 1;

	unsigned long pages_to_scan;

	pages_to_scan = ksm_scan_batch_pages;

	for (i = 0; i < ksm_scan_ladder_size; i++, mul *= ksm_scan_ratio_delta) {
		ksm_scan_ladder[i].scan_ratio = ksm_min_scan_ratio * mul;
		ksm_scan_ladder[i].pages_to_scan = pages_to_scan
			* ksm_scan_ladder[i].scan_ratio / KSM_SCAN_RATIO_MAX;
		INIT_LIST_HEAD(&ksm_scan_ladder[i].vma_list);
		//init_MUTEX(&ksm_scan_ladder[i].sem);
		ksm_scan_ladder[i].vma_num = 0;
		//ksm_scan_ladder[i].vma_finished = 0;
		ksm_scan_ladder[i].scan_turn = 1;
		ksm_scan_ladder[i].round_finished = 0;
		ksm_scan_ladder[i].fully_scanned_slots = 0;
	}
}

static inline int cal_positive_negative_costs(void)
{
	struct page *p1, *p2;
	unsigned char *addr1, *addr2;
	unsigned long i, time_start, checksum_cost, gcdval;
	unsigned long sample_num_stored = current_sample_num;
	unsigned long loopnum = 0;

	//printk(KERN_INFO "KSM: Calculating random sampling hash costs.\n");

	p1 = alloc_page(GFP_KERNEL);
	if (!p1)
		return -ENOMEM;

	p2 = alloc_page(GFP_KERNEL);
	if (!p2)
		return -ENOMEM;

	addr1 = kmap_atomic(p1, KM_USER0);
	addr2 = kmap_atomic(p2, KM_USER1);
	memset(addr1, random32(), PAGE_SIZE);
	memcpy(addr2, addr1, PAGE_SIZE);
	/* make sure that the two pages differ in last byte */
	addr2[PAGE_SIZE-1] = ~addr2[PAGE_SIZE-1];
	kunmap_atomic(addr2, KM_USER1);
	kunmap_atomic(addr1, KM_USER0);

	current_sample_num = HASH_STRENGTH_FULL;
	time_start = jiffies;
	while (jiffies - time_start < HASH_STRENGTH_FULL / 10) {
		for (i = 0; i < 100; i++) {
			calc_checksum(p1, 0);
		}
		loopnum += 100;
	}
	checksum_cost = 100 * (jiffies - time_start);
	rshash_cost = checksum_cost / HASH_STRENGTH_FULL;
	printk(KERN_INFO "KSM: checksum_cost = %lu.\n", rshash_cost);
	current_sample_num = sample_num_stored;

	time_start = jiffies;
	for (i = 0; i < loopnum; i++) {
		pages_identical(p1, p2);
	}
	memcmp_cost = 100 * (jiffies - time_start);
	printk(KERN_INFO "KSM: memcmp_cost = %lu.\n", memcmp_cost);
	gcdval = gcd(rshash_cost, memcmp_cost);
	rshash_cost /= gcdval;
	memcmp_cost /= gcdval;

	__free_page(p1);
	__free_page(p2);
	return 0;
}

static inline int init_random_sampling(void)
{
	unsigned long i;
	random_nums = kmalloc(PAGE_SIZE, GFP_KERNEL);
	if (!random_nums)
		return -ENOMEM;

	for (i = 0; i < HASH_STRENGTH_FULL; i++)
		random_nums[i] = i;

	for (i = 0; i < HASH_STRENGTH_FULL; i++) {
		unsigned long rand_range, swap_index, tmp;

		rand_range = HASH_STRENGTH_FULL - i;
		swap_index = random32() % rand_range;
		tmp = random_nums[i];
		random_nums[i] =  random_nums[swap_index];
		random_nums[swap_index] = tmp;
	}

	rshash_state.state = RSHASH_NEW;
	rshash_state.below_count = 0;
	rshash_state.lookup_window_index = 0;

	stable_tree_sample_num = current_sample_num;

	return cal_positive_negative_costs();
}

static int __init ksm_init(void)
{
	struct task_struct *ksm_thread;
	int err;
	unsigned int allocsize;
	unsigned int sr = ksm_min_scan_ratio;

	ksm_scan_ladder_size = 1;
	while (sr < KSM_SCAN_RATIO_MAX) {
		sr *= ksm_scan_ratio_delta;
		ksm_scan_ladder_size++;
	}
	ksm_scan_ladder = kzalloc(sizeof(struct scan_rung) *
				  ksm_scan_ladder_size, GFP_KERNEL);
	if (!ksm_scan_ladder) {
		printk(KERN_ERR "ksm scan ladder allocation failed, size=%d\n",
		       ksm_scan_ladder_size);
		err = ENOMEM;
		goto out;
	}
	init_scan_ladder();

	allocsize = KSM_DUP_VMA_MAX * KSM_DUP_VMA_MAX *
		sizeof(unsigned int) / 2;
	if (!(ksm_inter_vma_table = vmalloc(allocsize))) {
		err = ENOMEM;
		goto out_free3;
	}

	memset(ksm_inter_vma_table, 0, allocsize);

	ksm_vma_table = kzalloc(sizeof(struct vma_slot *) *
				ksm_vma_table_size, GFP_KERNEL);

	if (!ksm_vma_table) {
		printk(KERN_ERR "ksm_vma_table allocation failed, size=%d\n",
		       ksm_vma_table_size);
		err = ENOMEM;
		goto out;
	}

	err = init_random_sampling();
	if (err)
		goto out_free;

	err = ksm_slab_init();
	if (err)
		goto out_free4;

	ksm_thread = kthread_run(ksm_scan_thread, NULL, "ksmd");
	if (IS_ERR(ksm_thread)) {
		printk(KERN_ERR "ksm: creating kthread failed\n");
		err = PTR_ERR(ksm_thread);
		goto out_free1;
	}

#ifdef CONFIG_SYSFS
	err = sysfs_create_group(mm_kobj, &ksm_attr_group);
	if (err) {
		printk(KERN_ERR "ksm: register sysfs failed\n");
		kthread_stop(ksm_thread);
		goto out_free1;
	}
#else
	ksm_run = KSM_RUN_MERGE;	/* no way for user to start it */

#endif /* CONFIG_SYSFS */

#ifdef CONFIG_MEMORY_HOTREMOVE
	/*
	 * Choose a high priority since the callback takes ksm_thread_mutex:
	 * later callbacks could only be taking locks which nest within that.
	 */
	hotplug_memory_notifier(ksm_memory_callback, 100);
#endif
	return 0;

out_free1:
	ksm_slab_free();
out_free4:
	kfree(random_nums);
out_free:
	vfree(ksm_inter_vma_table);
out_free3:
	kfree(ksm_scan_ladder);

out:
	return err;
}

#ifdef MODULE
module_init(ksm_init)
#else
late_initcall(ksm_init);
#endif

