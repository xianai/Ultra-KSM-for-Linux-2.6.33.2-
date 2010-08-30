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

#include <asm/tlbflush.h>
#include "internal.h"

//#define CONFIG_KSM_SHA1 1

#define CONFIG_KSM_SUPERFASTHASH 1

#ifdef CONFIG_KSM_SHA1
#define KSM_CHECKSUM_SIZE	5
#else
#define KSM_CHECKSUM_SIZE	1
#endif

/*
 * A few notes about the KSM scanning process,
 * to make it easier to understand the data structures below:
 *
 * In order to reduce excessive scanning, KSM sorts the memory pages by their
 * contents into a data structure that holds pointers to the pages' locations.
 *
 * Since the contents of the pages may change at any moment, KSM cannot just
 * insert the pages into a normal sorted tree and expect it to find anything.
 * Therefore KSM uses two data structures - the stable and the unstable tree.
 *
 * The stable tree holds pointers to all the merged pages (ksm pages), sorted
 * by their contents.  Because each such page is write-protected, searching on
 * this tree is fully assured to be working (except when pages are unmapped),
 * and therefore this tree is called the stable tree.
 *
 * In addition to the stable tree, KSM uses a second data structure called the
 * unstable tree: this tree holds pointers to pages which have been found to
 * be "unchanged for a period of time".  The unstable tree sorts these pages
 * by their contents, but since they are not write-protected, KSM cannot rely
 * upon the unstable tree to work correctly - the unstable tree is liable to
 * be corrupted as its contents are modified, and so it is called unstable.
 *
 * KSM solves this problem by several techniques:
 *
 * 1) The unstable tree is flushed every time KSM completes scanning all
 *    memory areas, and then the tree is rebuilt again from the beginning.
 * 2) KSM will only insert into the unstable tree, pages whose hash value
 *    has not changed since the previous scan of all memory areas.
 * 3) The unstable tree is a RedBlack Tree - so its balancing is based on the
 *    colors of the nodes and not on their contents, assuring that even when
 *    the tree gets "corrupted" it won't get out of balance, so scanning time
 *    remains the same (also, searching and inserting nodes in an rbtree uses
 *    the same algorithm, so we have no overhead when we flush and rebuild).
 * 4) KSM never flushes the stable tree, which means that even if it were to
 *    take 10 attempts to find a page in the unstable tree, once it is found,
 *    it is secured in the stable tree.  (When we scan a new page, we first
 *    compare it against the stable tree, and then against the unstable tree.)
 */



/**
 * struct ksm_scan - cursor for scanning
 * @mm_slot: the current mm_slot we are scanning
 * @address: the next address inside that to be scanned
 * @rmap_list: link to the next rmap to be scanned in the rmap_list
 * @seqnr: count of completed full scans (needed when removing unstable node)
 *
 * There is only the one ksm_scan instance of this cursor structure.
 */
struct ksm_scan {
	struct mm_slot *mm_slot;
	unsigned long address;
	struct rmap_item **rmap_list;
	unsigned long seqnr;
};

/**
 * struct stable_node - node of the stable rbtree
 * @node: rb node of this ksm page in the stable tree
 * @hlist: hlist head of rmap_items using this ksm page
 * @kpfn: page frame number of this ksm page
 */
struct stable_node {
	struct rb_node node;
	struct hlist_head hlist;
	unsigned long kpfn;
	u32 checksum[KSM_CHECKSUM_SIZE];
	struct vm_area_struct *old_vma;
};

/**
 * struct rmap_item - reverse mapping item for virtual addresses
 * @rmap_list: next rmap_item in mm_slot's singly-linked rmap_list
 * @anon_vma: pointer to anon_vma for this mm,address, when in stable tree
 * @mm: the memory structure this rmap_item is pointing into
 * @address: the virtual address this rmap_item tracks (+ flags in low bits)
 * @oldchecksum: previous checksum of the page at that virtual address
 * @node: rb node of this rmap_item in the unstable tree
 * @head: pointer to stable_node heading this list in the stable tree
 * @hlist: link into hlist of rmap_items hanging off that stable_node
 */
struct rmap_item {
	struct rmap_item *rmap_list;
	struct anon_vma *anon_vma;	/* when stable */
	struct mm_struct *mm;
	unsigned long address;		/* + low bits used for flags below */
	/* which round is it, when this item is appended to tree */
	unsigned long scan_round;
	u32 oldchecksum[KSM_CHECKSUM_SIZE];	/* when unstable */
	union {
		struct rb_node node;	/* when node of unstable tree */
		struct {		/* when listed from stable tree */
			struct stable_node *head;
			struct hlist_node hlist;
		};
	};
};

#define SEQNR_MASK	0x0ff	/* low bits of unstable tree seqnr */
#define UNSTABLE_FLAG	0x100	/* is a node of the unstable tree */
#define STABLE_FLAG	0x200	/* is listed from the stable tree */

/* The stable and unstable tree heads */
static struct rb_root root_stable_tree = RB_ROOT;
static struct rb_root root_unstable_tree = RB_ROOT;


#define MM_SLOTS_HASH_HEADS 1024
static struct hlist_head *mm_slots_hash;

static struct mm_slot ksm_mm_head = {
	.mm_list = LIST_HEAD_INIT(ksm_mm_head.mm_list),
};
static struct ksm_scan ksm_scan = {
	.mm_slot = &ksm_mm_head,
};

static struct kmem_cache *rmap_item_cache;
static struct kmem_cache *stable_node_cache;
static struct kmem_cache *mm_slot_cache;

/* The number of nodes in the stable tree */
static unsigned long ksm_pages_shared;

/* The number of page slots additionally sharing those nodes */
static unsigned long ksm_pages_sharing;

/* The number of nodes in the unstable tree */
static unsigned long ksm_pages_unshared;

/* The number of rmap_items in use: to calculate pages_volatile */
static unsigned long ksm_rmap_items;

/* Number of pages ksmd should scan in one batch, in ratio of millionth */
static unsigned int ksm_batch_millionth_ratio = 10000;

/* Milliseconds ksmd should sleep between batches */
static unsigned int ksm_thread_sleep_mips_time = 1000;

/* minimum scan ratio for a vma, in unit of millionth */
static unsigned int ksm_min_scan_ratio = 10000;
#define KSM_SCAN_RATIO_MAX	1000000

/* Inter vma duplication number table page pointer array, initialized at startup */
#define KSM_DUP_VMA_MAX		1000
static unsigned int *ksm_inter_vma_table;

static struct vm_area_struct **ksm_vma_table;
static unsigned int ksm_vma_table_size = 10240;
static unsigned long ksm_vma_table_num = 0;

static unsigned long ksm_scan_round = 1;

/* How fast the scan ratio is changed */
static unsigned int ksm_scan_ratio_delta = 2;

/* Each rung of this ladder is a list of VMAs having a same scan ratio */
static struct scan_rung *ksm_scan_ladder;
static unsigned int ksm_scan_ladder_size;


#define KSM_RUN_STOP	0
#define KSM_RUN_MERGE	1
#define KSM_RUN_UNMERGE	2
static unsigned int ksm_run = KSM_RUN_STOP;

static unsigned int ksm_enable_full_scan = 0;

static DECLARE_WAIT_QUEUE_HEAD(ksm_thread_wait);
static DEFINE_MUTEX(ksm_thread_mutex);
static DEFINE_SPINLOCK(ksm_mmlist_lock);
static DEFINE_MUTEX(ksm_scan_sem);

#ifdef CONFIG_KSM_SHA1
/* for crypto hash functions */
static struct crypto_hash *ksm_hash_tfm;
#endif

#define KSM_KMEM_CACHE(__struct, __flags) kmem_cache_create("ksm_"#__struct,\
		sizeof(struct __struct), __alignof__(struct __struct),\
		(__flags), NULL)

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

	mm_slot_cache = KSM_KMEM_CACHE(mm_slot, 0);
	if (!mm_slot_cache)
		goto out_free2;

	return 0;

out_free2:
	kmem_cache_destroy(stable_node_cache);
out_free1:
	kmem_cache_destroy(rmap_item_cache);
out:
	return -ENOMEM;
}

static void __init ksm_slab_free(void)
{
	kmem_cache_destroy(mm_slot_cache);
	kmem_cache_destroy(stable_node_cache);
	kmem_cache_destroy(rmap_item_cache);
	mm_slot_cache = NULL;
}

static inline struct rmap_item *alloc_rmap_item(void)
{
	struct rmap_item *rmap_item;

	rmap_item = kmem_cache_zalloc(rmap_item_cache, GFP_KERNEL);
	if (rmap_item)
		ksm_rmap_items++;
	return rmap_item;
}

static inline void free_rmap_item(struct rmap_item *rmap_item)
{
	ksm_rmap_items--;
	rmap_item->mm = NULL;	/* debug safety */
	kmem_cache_free(rmap_item_cache, rmap_item);
}

static inline struct stable_node *alloc_stable_node(void)
{
	return kmem_cache_alloc(stable_node_cache, GFP_KERNEL | GFP_ATOMIC);
}

static inline void free_stable_node(struct stable_node *stable_node)
{
	kmem_cache_free(stable_node_cache, stable_node);
}

static inline struct mm_slot *alloc_mm_slot(void)
{
	if (!mm_slot_cache)	/* initialization failed */
		return NULL;
	return kmem_cache_zalloc(mm_slot_cache, GFP_KERNEL | GFP_ATOMIC);
}

/*
int ksm_fork(struct mm_struct *mm, struct mm_struct *oldmm)
{
	struct mm_slot *mm_slot;

        mm_slot = alloc_mm_slot();
        if (!mm_slot) {
                printk(KERN_ERR "ksm_enter failure, mm_slot allocation failed\n");
                return -ENOMEM;
        }

	if (test_bit(MMF_VM_MERGEABLE, &oldmm->flags))
		return __ksm_enter(mm_slot, mm);
	return 0;
}
*/


static inline void free_mm_slot(struct mm_slot *mm_slot)
{
	kmem_cache_free(mm_slot_cache, mm_slot);
}

static int __init mm_slots_hash_init(void)
{
	mm_slots_hash = kzalloc(MM_SLOTS_HASH_HEADS * sizeof(struct hlist_head),
				GFP_KERNEL);
	if (!mm_slots_hash)
		return -ENOMEM;
	return 0;
}

static void __init mm_slots_hash_free(void)
{
	kfree(mm_slots_hash);
}

static struct mm_slot *get_mm_slot(struct mm_struct *mm)
{
	struct mm_slot *mm_slot;
	struct hlist_head *bucket;
	struct hlist_node *node;

	bucket = &mm_slots_hash[((unsigned long)mm / sizeof(struct mm_struct))
				% MM_SLOTS_HASH_HEADS];
	hlist_for_each_entry(mm_slot, node, bucket, link) {
		if (mm == mm_slot->mm)
			return mm_slot;
	}
	return NULL;
}

static void insert_to_mm_slots_hash(struct mm_struct *mm,
				    struct mm_slot *mm_slot)
{
	struct hlist_head *bucket;

	bucket = &mm_slots_hash[((unsigned long)mm / sizeof(struct mm_struct))
				% MM_SLOTS_HASH_HEADS];
	mm_slot->mm = mm;
	hlist_add_head(&mm_slot->link, bucket);
}

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
		//cond_resched();
		page = follow_page(vma, addr, FOLL_GET);
		if (!page)
			break;
		if (PageKsm(page))
			ret = handle_mm_fault(vma->vm_mm, vma, addr,
							FAULT_FLAG_WRITE);
		else
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
	struct mm_struct *mm = rmap_item->mm;
	unsigned long addr = rmap_item->address;
	struct vm_area_struct *vma;

	/*
	 * It is not an accident that whenever we want to break COW
	 * to undo, we also need to drop a reference to the anon_vma.
	 */
	drop_anon_vma(rmap_item);

	down_read(&mm->mmap_sem);
	if (ksm_test_exit(mm))
		goto out;
	vma = find_vma(mm, addr);
	if (!vma || vma->vm_start > addr)
		goto out;
	if (!(vma->vm_flags & VM_MERGEABLE) || !vma->anon_vma)
		goto out;
	break_ksm(vma, addr);
out:
	up_read(&mm->mmap_sem);
}

static struct page *get_mergeable_page(struct rmap_item *rmap_item)
{
	struct mm_struct *mm = rmap_item->mm;
	unsigned long addr = rmap_item->address;
	struct vm_area_struct *vma;
	struct page *page;

	if (!down_read_trylock(&mm->mmap_sem))
		return NULL;

	if (ksm_test_exit(mm))
		goto out;
	vma = find_vma(mm, addr);
	if (!vma || vma->vm_start > addr)
		goto out;
	if (!(vma->vm_flags & VM_MERGEABLE) || !vma->anon_vma)
		goto out;

	page = follow_page(vma, addr, FOLL_GET);
	if (!page)
		goto out;
	if (PageAnon(page)) {
		flush_anon_page(vma, page, addr);
		flush_dcache_page(page);
	} else {
		put_page(page);
out:		page = NULL;
	}
	up_read(&mm->mmap_sem);
	return page;
}

static void remove_node_from_stable_tree(struct stable_node *stable_node)
{
	struct rmap_item *rmap_item;
	struct hlist_node *hlist;

	hlist_for_each_entry(rmap_item, hlist, &stable_node->hlist, hlist) {
		if (rmap_item->hlist.next)
			ksm_pages_sharing--;
		else
			ksm_pages_shared--;
		drop_anon_vma(rmap_item);
		rmap_item->address &= PAGE_MASK;
		//cond_resched();
	}

	rb_erase(&stable_node->node, &root_stable_tree);
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
static struct page *get_ksm_page(struct stable_node *stable_node)
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
	remove_node_from_stable_tree(stable_node);
	return NULL;
}



/*
 * Removing rmap_item from stable or unstable tree.
 * This function will clean the information from the stable/unstable tree.
 */
static void remove_rmap_item_from_tree(struct rmap_item *rmap_item)
{
	if (rmap_item->address & STABLE_FLAG) {
		struct stable_node *stable_node;
		struct page *page;

		stable_node = rmap_item->head;
		page = get_ksm_page(stable_node);
		if (!page)
			goto out;

		lock_page(page);
		hlist_del(&rmap_item->hlist);
		unlock_page(page);
		put_page(page);

		if (stable_node->hlist.first)
			ksm_pages_sharing--;
		else
			ksm_pages_shared--;

		drop_anon_vma(rmap_item);
		rmap_item->address &= PAGE_MASK;

	} else if (rmap_item->address & UNSTABLE_FLAG) {
		unsigned char age;

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
		if (rmap_item->scan_round == ksm_scan_round)
			rb_erase(&rmap_item->node, &root_unstable_tree);
		ksm_pages_unshared--;
		rmap_item->address &= PAGE_MASK;
	}
out:
	//cond_resched();		/* we're called from many long loops */
	return;
}

/* can be refactored & beautified */
static void ksm_intertab_clear(struct vm_area_struct *vma)
{
	int i;
	unsigned index;

	for (i = 0; i <= vma->ksm_index; i++) {
		index = intertab_vma_offset(vma->ksm_index, i);
		ksm_inter_vma_table[index] = 0; /* Cleared data for this round */
	}

	for (i = vma->ksm_index + 1; i < ksm_vma_table_num; i++) {
		index = intertab_vma_offset(vma->ksm_index, i);
		ksm_inter_vma_table[index] = 0;
	}

}

void ksm_remove_vma(struct vm_area_struct *vma)
{
	struct rmap_item *rmap, *rmap_old;
	int i;

	if (list_empty(&vma->ksm_list) || !vma->rung)
	    return;

	mutex_lock(&ksm_scan_sem);
	if (vma->rung->current_scan == &vma->ksm_list)
		vma->rung->current_scan = vma->rung->current_scan->next;

	list_del_init(&vma->ksm_list);

	if (vma->rung->current_scan == &vma->rung->vma_list) {
		/* This rung finishes a round */
		vma->rung->round_finished = 1;
		vma->rung->current_scan = vma->rung->vma_list.next;
	}

	for (i = 0; i < ksm_vma_table_size; i++) {
		if ((vma == ksm_vma_table[i])) {
			//cal_dedup_ratio_clear(vma);
			ksm_intertab_clear(vma);
			ksm_vma_table_num--;
			ksm_vma_table[i] = NULL;
			break;
		}
	}

	rmap = vma->rmap_list;
	rmap_old = NULL;

	while (rmap) {
		rmap_old = rmap;
		rmap = rmap->rmap_list;
		remove_rmap_item_from_tree(rmap_old);
		free_rmap_item(rmap_old);
	}
	mutex_unlock(&ksm_scan_sem);
}

static void remove_trailing_rmap_items(struct mm_slot *mm_slot,
				       struct rmap_item **rmap_list)
{
	while (*rmap_list) {
		struct rmap_item *rmap_item = *rmap_list;
		*rmap_list = rmap_item->rmap_list;
		remove_rmap_item_from_tree(rmap_item);
		free_rmap_item(rmap_item);
	}
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

#ifdef CONFIG_SYSFS
/*
 * Only called through the sysfs control interface:
 */
static int unmerge_and_remove_all_rmap_items(void)
{
	struct mm_slot *mm_slot;
	struct mm_struct *mm;
	struct vm_area_struct *vma;
	int err = 0;

	spin_lock(&ksm_mmlist_lock);
	ksm_scan.mm_slot = list_entry(ksm_mm_head.mm_list.next,
						struct mm_slot, mm_list);
	spin_unlock(&ksm_mmlist_lock);

	for (mm_slot = ksm_scan.mm_slot;
			mm_slot != &ksm_mm_head; mm_slot = ksm_scan.mm_slot) {
		mm = mm_slot->mm;
		down_read(&mm->mmap_sem);
		for (vma = mm->mmap; vma; vma = vma->vm_next) {
			if (ksm_test_exit(mm))
				break;
			if (!(vma->vm_flags & VM_MERGEABLE) || !vma->anon_vma)
				continue;
			err = unmerge_ksm_pages(vma,
						vma->vm_start, vma->vm_end);
			if (err)
				goto error;
		}

		remove_trailing_rmap_items(mm_slot, &mm_slot->rmap_list);

		spin_lock(&ksm_mmlist_lock);
		ksm_scan.mm_slot = list_entry(mm_slot->mm_list.next,
						struct mm_slot, mm_list);
		if (ksm_test_exit(mm)) {
			hlist_del(&mm_slot->link);
			list_del(&mm_slot->mm_list);
			spin_unlock(&ksm_mmlist_lock);

			free_mm_slot(mm_slot);
			clear_bit(MMF_VM_MERGEABLE, &mm->flags);
			up_read(&mm->mmap_sem);
			mmdrop(mm);
		} else {
			spin_unlock(&ksm_mmlist_lock);
			up_read(&mm->mmap_sem);
		}
	}

	ksm_scan.seqnr = 0;
	return 0;

error:
	up_read(&mm->mmap_sem);
	spin_lock(&ksm_mmlist_lock);
	ksm_scan.mm_slot = &ksm_mm_head;
	spin_unlock(&ksm_mmlist_lock);
	return err;
}
#endif /* CONFIG_SYSFS */

#if !defined (get16bits)
	#define get16bits(d) ((((uint32_t)(((const uint8_t *)(d))[1])) << 8)\
                       +(uint32_t)(((const uint8_t *)(d))[0]) )
#endif

#ifdef CONFIG_KSM_SUPERFASTHASH
static uint32_t SuperFastHash (const char * data, int len) {
	uint32_t hash = len, tmp;
	int rem;

	if (len <= 0 || data == NULL) return 0;

	rem = len & 3;
	len >>= 2;

	/* Main loop */
	for (;len > 0; len--) {
		hash  += get16bits (data);
		tmp    = (get16bits (data+2) << 11) ^ hash;
		hash   = (hash << 16) ^ tmp;
		data  += 2*sizeof (uint16_t);
		hash  += hash >> 11;
	}

	/* Handle end cases */
	switch (rem) {
	case 3: hash += get16bits (data);
		hash ^= hash << 16;
		hash ^= data[sizeof (uint16_t)] << 18;
		hash += hash >> 11;
		break;
	case 2: hash += get16bits (data);
		hash ^= hash << 11;
		hash += hash >> 17;
		break;
	case 1: hash += *data;
		hash ^= hash << 10;
		hash += hash >> 1;
	}

	/* Force "avalanching" of final 127 bits */
	hash ^= hash << 3;
	hash += hash >> 5;
	hash ^= hash << 4;
	hash += hash >> 17;
	hash ^= hash << 25;
	hash += hash >> 6;

	return hash;
}
#endif

static void calc_checksum(struct page *page, u32 *checksum)
{


#ifdef CONFIG_KSM_SHA1
	struct hash_desc desc;
	struct scatterlist sg[1];

	sg_init_table(sg, 1);
	sg_set_page(sg, page, PAGE_SIZE, 0);

	desc.tfm = ksm_hash_tfm;
	desc.flags = 0;
	if (crypto_hash_digest(&desc, sg, PAGE_SIZE, (u8*)checksum)) {
		printk(KERN_ERR "Ksm hash digest failed\n");
	}
#else
	//checksum = jhash2(addr, PAGE_SIZE / 4, 17);
	void *addr = kmap_atomic(page, KM_USER0);

#ifdef CONFIG_KSM_SUPERFASTHASH
	*checksum = SuperFastHash(addr, PAGE_SIZE);
#else
	*checksum = jhash2(addr, PAGE_SIZE / 4, 17);
#endif

	kunmap_atomic(addr, KM_USER0);
#endif

	return;
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
			      pte_t *orig_pte)
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

/**
 * replace_page - replace page in vma by new ksm page
 * @vma:      vma that holds the pte pointing to page
 * @page:     the page we are replacing by kpage
 * @kpage:    the ksm page we replace page by
 * @orig_pte: the original value of the pte
 *
 * Returns 0 on success, -EFAULT on failure.
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
	int err = -EFAULT;

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
	int err = -EFAULT;

	if (page == kpage) {			/* ksm page forked */
		if (same_page)
			*same_page = 1;
		return 0;
	}

	if (same_page)
		*same_page = 0;


	if (!(vma->vm_flags & VM_MERGEABLE))
		goto out;
	if (!PageAnon(page))
		goto out;

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
	if (write_protect_page(vma, page, &orig_pte) == 0) {
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
		} else if (pages_identical(page, kpage)) {
			err = replace_page(vma, page, kpage, orig_pte);
			//if (!err)
				//merged = 1;
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
	struct mm_struct *mm = rmap_item->mm;
	struct vm_area_struct *vma;
	int err = -EFAULT;

	down_read(&mm->mmap_sem);
	if (ksm_test_exit(mm))
		goto out;
	vma = find_vma(mm, rmap_item->address);
	if (!vma || vma->vm_start > rmap_item->address)
		goto out;

	err = try_to_merge_one_page(vma, page, kpage, same_page);
	if (err)
		goto out;

	/* Must get reference to anon_vma while still holding mmap_sem */
	hold_anon_vma(rmap_item, vma->anon_vma);
out:
	up_read(&mm->mmap_sem);
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
static struct page *try_to_merge_two_pages(struct rmap_item *rmap_item,
					   struct page *page,
					   struct rmap_item *tree_rmap_item,
					   struct page *tree_page)
{
	int err;

	err = try_to_merge_with_ksm_page(rmap_item, page, NULL, NULL);
	if (!err) {
		err = try_to_merge_with_ksm_page(tree_rmap_item,
						tree_page, page, NULL);
		/*
		 * If that fails, we have a ksm page with only one pte
		 * pointing to it: so break it.
		 */
		if (err)
			break_cow(rmap_item);
	}
	return err ? NULL : page;
}


static int checksum_compare(u32 *c1, u32 *c2)
{
#ifdef CONFIG_KSM_SHA1
	int i = 0;
	while ((c1[i] == c2[i]) && (i < 5))
		i++;

	if (i >= 5)
		return 0;
	else if(c1[i] > c2[i])
		return 1;
	else
		return -1;
#else
	if (*c1 > *c2)
		return 1;
	else if (*c1 < *c2)
		return -1;
	else
		return 0;
#endif
}

static inline void checksum_copy2(u32 *src, u32 *dst)
{
	int i;

	for (i = 0; i < KSM_CHECKSUM_SIZE; i++) {
		dst[i] = src[i];
	}
	return;
}

/*
 * stable_tree_search - search for page inside the stable tree
 *
 * This function checks if there is a page inside the stable tree
 * with identical content to the page that we are scanning right now.
 *
 * This function returns the stable tree node of identical content if found,
 * NULL otherwise.
 */
static struct page *stable_tree_search(struct page *page, u32 *checksum)
{
	struct rb_node *node = root_stable_tree.rb_node;
	struct stable_node *stable_node;

	stable_node = page_stable_node(page);
	if (stable_node) {			/* ksm page forked */
		get_page(page);
		return page;
	}

	while (node) {
		struct page *tree_page;
		int cmp;

		//cond_resched();
		stable_node = rb_entry(node, struct stable_node, node);

		tree_page = get_ksm_page(stable_node);
		if (!tree_page)
			return NULL;

		//ret = memcmp_pages(page, tree_page);
		cmp = checksum_compare(checksum, stable_node->checksum);

		if (cmp < 0) {
			put_page(tree_page);
			node = node->rb_left;
		} else if (cmp > 0) {
			put_page(tree_page);
			node = node->rb_right;
		} else
			return tree_page;
	}

	return NULL;
}

/*
 * stable_tree_insert - insert rmap_item pointing to new ksm page
 * into the stable tree.
 *
 * This function returns the stable tree node just allocated on success,
 * NULL otherwise.
 */
static struct stable_node *stable_tree_insert(struct page *kpage)
{
	struct rb_node **new = &root_stable_tree.rb_node;
	struct rb_node *parent = NULL;
	struct stable_node *stable_node;
	u32 checksum[KSM_CHECKSUM_SIZE];

	/* now it's write_protected, re-calc checksum */
	calc_checksum(kpage, checksum);

	while (*new) {
		struct page *tree_page;
		int cmp, ret;

		//cond_resched();
		stable_node = rb_entry(*new, struct stable_node, node);
/*
		tree_page = get_ksm_page(stable_node);
		if (!tree_page)
			return NULL;

		ret = memcmp_pages(kpage, tree_page);
		put_page(tree_page);
*/
		cmp = checksum_compare(checksum, stable_node->checksum);

		parent = *new;
		if (cmp < 0)
			new = &parent->rb_left;
		else if (cmp > 0)
			new = &parent->rb_right;
		else {
			/*
			 * It is not a bug that stable_tree_search() didn't
			 * find this node: because at that time our page was
 			   not yet write-protected, so may have changed since.
 			   In addition, we must check if it's a hash collision.
			 */
			tree_page = get_ksm_page(stable_node);
			if (!tree_page)
				return NULL;

			ret = memcmp_pages(kpage, tree_page);
			put_page(tree_page);

			if (!ret)
				return NULL;
			else
				BUG(); /* TODO: deal with hash collision*/
		}
	}

	stable_node = alloc_stable_node();
	if (!stable_node)
		return NULL;

	rb_link_node(&stable_node->node, parent, new);
	rb_insert_color(&stable_node->node, &root_stable_tree);

	INIT_HLIST_HEAD(&stable_node->hlist);

	stable_node->kpfn = page_to_pfn(kpage);
	checksum_copy2(checksum, stable_node->checksum);
	set_page_stable_node(kpage, stable_node);

	return stable_node;
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
					      struct page *page,
					      struct page **tree_pagep,
					      u32 *checksum)

{
	struct rb_node **new = &root_unstable_tree.rb_node;
	struct rb_node *parent = NULL;

	while (*new) {
		struct rmap_item *tree_rmap_item;
		struct page *tree_page;
		int cmp;

		//cond_resched();
		tree_rmap_item = rb_entry(*new, struct rmap_item, node);
		tree_page = get_mergeable_page(tree_rmap_item);
		if (!tree_page)
			return NULL;

		/*
		 * Don't substitute a ksm page for a forked page.
		 */
		if (page == tree_page) {
			put_page(tree_page);
			return NULL;
		}

		//ret = memcmp_pages(page, tree_page);
		cmp = checksum_compare(checksum, tree_rmap_item->oldchecksum);

		parent = *new;
		if (cmp < 0) {
			put_page(tree_page);
			new = &parent->rb_left;
		} else if (cmp > 0) {
			put_page(tree_page);
			new = &parent->rb_right;
		} else {
			*tree_pagep = tree_page;
			return tree_rmap_item;
		}
	}

	rmap_item->address |= UNSTABLE_FLAG;
	//rmap_item->address |= (ksm_scan.seqnr & SEQNR_MASK);
	rmap_item->scan_round = ksm_scan_round;
	checksum_copy2(checksum, rmap_item->oldchecksum);
	rb_link_node(&rmap_item->node, parent, new);
	rb_insert_color(&rmap_item->node, &root_unstable_tree);

	ksm_pages_unshared++;
	return NULL;
}

/*
 * stable_tree_append - add another rmap_item to the linked list of
 * rmap_items hanging off a given node of the stable tree, all sharing
 * the same ksm page.
 */
static void stable_tree_append(struct rmap_item *rmap_item,
			       struct stable_node *stable_node)
{
	rmap_item->head = stable_node;
	rmap_item->address |= STABLE_FLAG;
	rmap_item->scan_round = ksm_scan_round;
	hlist_add_head(&rmap_item->hlist, &stable_node->hlist);

	if (rmap_item->hlist.next)
		ksm_pages_sharing++;
	else
		ksm_pages_shared++;
}


static void enter_inter_vma_table(struct vm_area_struct *vma)
{
	unsigned int i;

	for (i = 0; i < ksm_vma_table_size; i++) {
		if (!ksm_vma_table[i])
			break;
	}
	vma->ksm_index = i;
	ksm_vma_table[i] = vma;
	ksm_vma_table_num++;
}

static void adjust_intertab_pair(struct vm_area_struct *vma1,
				 struct vm_area_struct *vma2)
{
	unsigned long offset;

	if (vma1->ksm_index == -1)
		enter_inter_vma_table(vma1);

	if (vma2->ksm_index == -1)
		enter_inter_vma_table(vma2);

	offset = intertab_vma_offset(vma1->ksm_index, vma2->ksm_index);
	ksm_inter_vma_table[offset]++;
	BUG_ON(!ksm_inter_vma_table[offset]);
}

static void update_intertab_unstable(struct rmap_item *item1,
				     struct rmap_item *item2)
{
	struct vm_area_struct *vma1, *vma2;

	list_for_each_entry(vma1, &item1->anon_vma->head, anon_vma_node) {
		list_for_each_entry(vma2, &item2->anon_vma->head,
				    anon_vma_node) {
			adjust_intertab_pair(vma1, vma2);
		}
	}
}

static void update_intertab_stable(struct rmap_item *in_item, struct page *kpage)
{

	struct vm_area_struct *vma1, *vma2;
	struct stable_node *node;
	struct rmap_item *item;
	struct hlist_node *n;

	node = page_stable_node(kpage);

	hlist_for_each_entry(item, n, &node->hlist, hlist) {
		if (item->scan_round == ksm_scan_round) {
			list_for_each_entry(vma1, &item->anon_vma->head,
					    anon_vma_node) {
				list_for_each_entry(vma2,
						    &in_item->anon_vma->head,
						    anon_vma_node){
					adjust_intertab_pair(vma1, vma2);
				}
			}
		}
	}

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
static void cmp_and_merge_page(struct page *page, struct rmap_item *rmap_item)
{
	struct rmap_item *tree_rmap_item;
	struct page *tree_page = NULL;
	struct stable_node *stable_node;
	struct page *kpage;
	u32 checksum[KSM_CHECKSUM_SIZE];
	int err;
	unsigned int same_page;

	remove_rmap_item_from_tree(rmap_item);

	calc_checksum(page, checksum);
	/* We first start with searching the page inside the stable tree */
	kpage = stable_tree_search(page, checksum);
	if (kpage) {
		err = try_to_merge_with_ksm_page(rmap_item, page,
						 kpage, &same_page);
		if (!err) {
			/*
			 * The page was successfully merged:
			 * add its rmap_item to the stable tree.
			 */
			lock_page(kpage);
			stable_tree_append(rmap_item, page_stable_node(kpage));
			if (!same_page)
				update_intertab_stable(rmap_item, kpage);
			unlock_page(kpage);
		}
		put_page(kpage);
		return;
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
		unstable_tree_search_insert(rmap_item, page, &tree_page, checksum);
	if (tree_rmap_item) {
		kpage = try_to_merge_two_pages(rmap_item, page,
						tree_rmap_item, tree_page);
		put_page(tree_page);
		/*
		 * As soon as we merge this page, we want to remove the
		 * rmap_item of the page we have merged with from the unstable
		 * tree, and insert it instead as new node in the stable tree.
		 */
		if (kpage) {
			update_intertab_unstable(rmap_item, tree_rmap_item);
			remove_rmap_item_from_tree(tree_rmap_item);
			lock_page(kpage);
			stable_node = stable_tree_insert(kpage);
			if (stable_node) {
				stable_tree_append(tree_rmap_item, stable_node);
				stable_tree_append(rmap_item, stable_node);
			}
			unlock_page(kpage);

			/*
			 * If we fail to insert the page into the stable tree,
			 * we will have 2 virtual addresses that are pointing
			 * to a ksm page left outside the stable tree,
			 * in which case we need to break_cow on both.
			 */
			if (!stable_node) {
				break_cow(tree_rmap_item);
				break_cow(rmap_item);
			}
		}
	}
}

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
		/* It has already been zeroed */
		rmap_item_new->mm = vma->vm_mm;
		rmap_item_new->address = addr;
		rmap_item_new->rmap_list = rmap_item;

		if (rmap_item_old)
			rmap_item_old->rmap_list = rmap_item;
		else
			vma->rmap_list = rmap_item_new;
		rmap_item = rmap_item_new;
	}
	return rmap_item;
}

static inline int vma_need_scan(struct vm_area_struct *vma)
{
	return vma->vm_flags & VM_MERGEABLE;
}

static void scan_vma_one_page(struct vm_area_struct *vma)
{
	struct mm_struct *mm;
	unsigned long pages, addr;
	struct page *page;
	//struct mm_slot *slot;
	struct rmap_item *rmap_item;



	mm = vma->vm_mm;
	if (!mm)
		return;

	BUG_ON(!vma_need_scan(vma));

	down_read(&mm->mmap_sem);
	if (ksm_test_exit(mm))
		goto out1;

	pages = (vma->vm_end - vma->vm_start) / PAGE_SIZE;
	addr = vma->vm_start + (random32() % pages) * PAGE_SIZE;

	//slot = get_mm_slot(mm);
	//BUG_ON(!slot);

	page = follow_page(vma, addr, FOLL_GET);

	if (!page)
		goto out1;

	if (!PageAnon(page)) {
		goto out2;
	}

	flush_anon_page(vma, page, addr);
	flush_dcache_page(page);
	rmap_item = get_next_rmap_item(vma, addr);
	if (!rmap_item) {
		goto out2;
	}

	if (PageKsm(page) && in_stable_tree(rmap_item))
		goto out2;

	/* change inter vma state in cmp_and_merge_page */
	cmp_and_merge_page(page, rmap_item);
out2:
	put_page(page);
out1:
	up_read(&mm->mmap_sem);
	return;
}

static inline unsigned long get_random_sample_num(unsigned long total,
						  unsigned long needed)
{
	unsigned long ret, test_needed, range_bottom, range_top;

	/* It can be proved that ret/needed <= 30/13 */
	range_top = needed * 30 / 13;
	range_bottom = needed;

	BUG_ON(total == 0);

	do {
		ret = (range_top + range_bottom) / 2;
		test_needed = ret - ret * ret * 9 / (10 * total) +
			+ ret * ret * ret / (3 * total * total);

		if (test_needed > needed)
			range_top = ret;
		else
			range_bottom = ret;

	} while (test_needed != needed);

	return ret;
}

static unsigned long get_vma_random_scan_num(struct vm_area_struct *vma,
					     unsigned long scan_ratio)
{
	unsigned long len, needed;

	len = vma->vm_end - vma->vm_start;
	len /= PAGE_SIZE;
	needed = len * scan_ratio / KSM_SCAN_RATIO_MAX;

	if (!needed)
		needed = 1;

	return get_random_sample_num(len, needed);
}

static inline void vma_rung_enter(struct vm_area_struct *vma,
				  struct scan_rung *rung)
{
	/* leave the old rung it was in */
	if (!list_empty(&vma->ksm_list)) {
		if (vma->rung->current_scan == &vma->ksm_list)
			vma->rung->current_scan = vma->ksm_list.next;
		list_del_init(&vma->ksm_list);

		if (vma->rung->current_scan == &rung->vma_list) {
			/* This rung finishes a round */
			rung->round_finished = 1;
			rung->current_scan = rung->vma_list.next;
		}
	}

	/* enter the new rung */
	if (list_empty(&rung->vma_list))
		rung->current_scan = &vma->ksm_list;
	list_add_tail(&vma->ksm_list, &rung->vma_list);
	vma->rung = rung;
	vma->pages_to_scan = get_vma_random_scan_num(vma, rung->scan_ratio);
}

static inline void vma_rung_up(struct vm_area_struct *vma)
{
	if (vma->rung == &ksm_scan_ladder[ksm_scan_ladder_size-1])
		return;

	vma_rung_enter(vma, vma->rung + 1);
}

static inline void vma_rung_down(struct vm_area_struct *vma)
{
	if (vma->rung == &ksm_scan_ladder[0])
		return;

	vma_rung_enter(vma, vma->rung - 1);
}

/* can be refactored & beautified */
static unsigned long cal_dedup_ratio_clear(struct vm_area_struct *vma)
{
	int i;
	unsigned long dedup_num = 0;
	unsigned index;

	for (i = 0; i < vma->ksm_index; i++) {
		index = intertab_vma_offset(vma->ksm_index, i);
		dedup_num += ksm_inter_vma_table[index]
		* KSM_SCAN_RATIO_MAX / ksm_scan_ladder[vma->ksm_index].scan_ratio
		* KSM_SCAN_RATIO_MAX / ksm_scan_ladder[i].scan_ratio;
		ksm_inter_vma_table[index] = 0; /* Cleared data for this round */
	}

	for (i = vma->ksm_index + 1; i < ksm_vma_table_num; i++) {
		index = intertab_vma_offset(vma->ksm_index, i);
		dedup_num += ksm_inter_vma_table[index]
		* KSM_SCAN_RATIO_MAX / ksm_scan_ladder[vma->ksm_index].scan_ratio
		* KSM_SCAN_RATIO_MAX / ksm_scan_ladder[i].scan_ratio;
		ksm_inter_vma_table[index] = 0;
	}

	index = intertab_vma_offset(vma->ksm_index, vma->ksm_index);
	dedup_num += ksm_inter_vma_table[index]
		     * KSM_SCAN_RATIO_MAX / ksm_scan_ladder[i].scan_ratio;
	ksm_inter_vma_table[index] = 0;

	return (dedup_num /
		((vma->vm_end - vma->vm_start) / PAGE_SIZE *
		 ksm_scan_ladder[vma->ksm_index].scan_ratio /
		 KSM_SCAN_RATIO_MAX) * KSM_SCAN_RATIO_MAX);
}

static void round_update_ladder(void)
{
	int i;
	struct vm_area_struct *vma;
	unsigned long dedup_ratio_max = 0, dedup_ratio_mean = 0;
	unsigned long num = 0, threshold;

	for (i = 0; i < ksm_vma_table_size; i++) {
		if ((vma = ksm_vma_table[i])) {
			num++;
			vma->dedup_ratio = cal_dedup_ratio_clear(vma);
			if (dedup_ratio_max < vma->dedup_ratio)
				dedup_ratio_max = vma->dedup_ratio;
			dedup_ratio_mean += vma->dedup_ratio;
		}
	}

 	/* no vma has entered inter ref table, so no need to update
	their rung position */
	if (!num)
		goto out;

	dedup_ratio_mean /= num;
	threshold = (dedup_ratio_max + dedup_ratio_mean) / 2;

	for (i = 0; i < ksm_vma_table_size; i++) {
		if ((vma = ksm_vma_table[i])) {
			if (vma->dedup_ratio  &&
			    vma->dedup_ratio >= threshold) {
				vma_rung_up(vma);
			} else {
				vma_rung_down(vma);
			}
		}
	}

out:
	for (i = 0; i < ksm_scan_ladder_size; i++)
		ksm_scan_ladder[i].round_finished = 0;

}

static inline unsigned int ksm_pages_to_scan(unsigned int millionth_ratio)
{
	return totalram_pages * millionth_ratio / 1000000;
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
	unsigned long num, scan_bonus = 0;
	struct vm_area_struct *vma;
	struct list_head *next_scan;
	unsigned char round_finished = 1;
	int i;


	//printk(KERN_ERR "****ksm_do_scan****\n");
	for (i = ksm_scan_ladder_size - 1; i >= 0; i--) {
		struct scan_rung *rung = &ksm_scan_ladder[i];
		if (list_empty(&rung->vma_list))
			continue;

		if (rung->round_finished) {
			scan_bonus += rung->pages_to_scan;
			continue;
		}

		rung->pages_to_scan += scan_bonus;
		if (!rung->pages_to_scan)
			continue;

		while (rung->pages_to_scan) {
			mutex_lock(&ksm_scan_sem);
			vma = list_entry(rung->current_scan,
					 struct vm_area_struct, ksm_list);

			if (vma->pages_scanned > vma->pages_to_scan) {
				printk(KERN_ERR "Bug on pages_scanned=%lu pages_to_scan=%lu",
				       vma->pages_scanned , vma->pages_to_scan);
			}

			BUG_ON(list_empty(&vma->ksm_list));

			if (vma->pages_scanned == vma->pages_to_scan) {
				vma->pages_scanned = 0;
				next_scan = rung->current_scan->next;
				if (next_scan == &rung->vma_list) {
					/* This rung finishes a round */
					rung->round_finished = 1;
					rung->current_scan = rung->vma_list.next;
					mutex_unlock(&ksm_scan_sem);
					break;
				} else {
					rung->current_scan = next_scan;
					vma = list_entry(rung->current_scan,
							 struct vm_area_struct,
							 ksm_list);
				}
			}
			scan_vma_one_page(vma);
			vma->pages_scanned++;
			rung->pages_to_scan--;
			mutex_unlock(&ksm_scan_sem);
		}

	}

	for (i = 0; i < ksm_scan_ladder_size; i++) {
		struct scan_rung *rung = &ksm_scan_ladder[i];

		if (!list_empty(&rung->vma_list) && !rung->round_finished) {
			round_finished = 0;
			break;
		}
	}

	mutex_lock(&ksm_scan_sem);
	if (round_finished) {
		round_update_ladder();

		/* sync with ksm_remove_vma for rb_erase */
		ksm_scan_round++;
		root_unstable_tree = RB_ROOT;
	}
	cal_ladder_pages_to_scan(ksm_pages_to_scan(ksm_batch_millionth_ratio));
	mutex_unlock(&ksm_scan_sem);
}

static int ksmd_should_run(void)
{
	return (ksm_run & KSM_RUN_MERGE) &&
		(!list_empty(&ksm_mm_head.mm_list) || ksm_enable_full_scan);
}

static inline unsigned int ksm_mips_time_to_jiffies(unsigned int mips_time)
{
	return mips_time * 500000  / loops_per_jiffy;
}


static void try_ksm_enter_all_process(void)
{
	struct mm_struct *mm;
	struct task_struct *p;
	int err;

/*
	mm_slot = alloc_mm_slot();
	if (!mm_slot) {
		printk(KERN_ERR "ksm_enter failure, mm_slot allocation failed\n");
		return;
	}
*/
	read_lock(&tasklist_lock);

	for_each_process(p) {
		if (!p->mm || p->flags & PF_KTHREAD ||
		    test_bit(MMF_VM_MERGEABLE, &p->mm->flags))
			continue;

		mm = get_task_mm(p);

		//printk(KERN_ERR "Adding new task %s\n", mm->owner->comm);
		if (mm) {
			if (!down_read_trylock(&mm->mmap_sem))
				goto out;

			err = __ksm_enter(p->mm);
			if (err) {
				printk(KERN_ERR "ksm_enter failure\n");
			}
			up_read(&mm->mmap_sem);
			mmput(mm);
		}
	}

out:
	read_unlock(&tasklist_lock);

	return;
}

static int ksm_scan_thread(void *nothing)
{
	set_user_nice(current, 5);

	while (!kthread_should_stop()) {
		if (ksm_enable_full_scan) {
			try_ksm_enter_all_process();
		}

		mutex_lock(&ksm_thread_mutex);
		if (ksmd_should_run())
			ksm_do_scan();
		mutex_unlock(&ksm_thread_mutex);

		if (ksmd_should_run()) {
			schedule_timeout_interruptible(
				ksm_mips_time_to_jiffies(ksm_thread_sleep_mips_time));
		} else {
			wait_event_interruptible(ksm_thread_wait,
				ksmd_should_run() || kthread_should_stop());
		}
	}
	return 0;
}

static void ksm_vma_enter(struct vm_area_struct *vma)
{
	//spin_lock(&ksm_scan_ladder_lock);

	if (list_empty(&ksm_scan_ladder[0].vma_list))
		ksm_scan_ladder[0].current_scan = &vma->ksm_list;

	list_add_tail(&vma->ksm_list, &ksm_scan_ladder[0].vma_list);
	vma->rung = &ksm_scan_ladder[0];
	vma->pages_to_scan = get_vma_random_scan_num(vma, vma->rung->scan_ratio);
	//spin_unlock(&ksm_scan_ladder_lock);
}

int __ksm_enter(struct mm_struct *mm)
{
	struct vm_area_struct *vma;
	struct mm_slot *mm_slot;
//	int needs_wakeup;
	mm_slot = alloc_mm_slot();
	if (!mm_slot)
		return -ENOMEM;

	/* Check ksm_run too?  Would need tighter locking */
//	needs_wakeup = list_empty(&ksm_mm_head.mm_list);


	if (strcmp(mm->owner->comm, "best_case"))
		return 0;



	spin_lock(&ksm_mmlist_lock);
	insert_to_mm_slots_hash(mm, mm_slot);
	/*
	 * Insert just behind the scanning cursor, to let the area settle
	 * down a little; when fork is followed by immediate exec, we don't
	 * want ksmd to waste time setting up and tearing down an rmap_list.
	 */
	list_add_tail(&mm_slot->mm_list, &ksm_scan.mm_slot->mm_list);
	spin_unlock(&ksm_mmlist_lock);

	set_bit(MMF_VM_MERGEABLE, &mm->flags);
	atomic_inc(&mm->mm_count);



	for (vma = mm->mmap; vma; vma = vma->vm_next) {
		//struct scan_rung *rung;

		if (vma->vm_flags & VM_MERGEABLE)
			continue;

		if (vma->vm_flags & (VM_PFNMAP | VM_IO  | VM_DONTEXPAND |
				     VM_RESERVED  | VM_HUGETLB | VM_INSERTPAGE |
				     VM_NONLINEAR | VM_MIXEDMAP | VM_SAO))
			continue;

		vma->vm_flags |= VM_MERGEABLE;
		BUG_ON(!list_empty(&vma->ksm_list));

		ksm_vma_enter(vma);
	}

//	if (needs_wakeup)
//		wake_up_interruptible(&ksm_thread_wait);

	return 0;
}

void __ksm_exit(struct mm_struct *mm)
{
	struct mm_slot *mm_slot;
	int easy_to_free = 0;

	/*
	 * This process is exiting: if it's straightforward (as is the
	 * case when ksmd was never running), free mm_slot immediately.
	 * But if it's at the cursor or has rmap_items linked to it, use
	 * mmap_sem to synchronize with any break_cows before pagetables
	 * are freed, and leave the mm_slot on the list for ksmd to free.
	 * Beware: ksm may already have noticed it exiting and freed the slot.
	 */

	spin_lock(&ksm_mmlist_lock);
	mm_slot = get_mm_slot(mm);
	if (mm_slot && ksm_scan.mm_slot != mm_slot) {
		if (!mm_slot->rmap_list) {
			hlist_del(&mm_slot->link);
			list_del(&mm_slot->mm_list);
			easy_to_free = 1;
		} else {
			list_move(&mm_slot->mm_list,
				  &ksm_scan.mm_slot->mm_list);
		}
	}
	spin_unlock(&ksm_mmlist_lock);

	if (easy_to_free) {
		free_mm_slot(mm_slot);
		clear_bit(MMF_VM_MERGEABLE, &mm->flags);
		mmdrop(mm);
	} else if (mm_slot) {
		down_write(&mm->mmap_sem);
		up_write(&mm->mmap_sem);
	}
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
	struct rmap_item *rmap_item;
	struct hlist_node *hlist;
	unsigned int mapcount = page_mapcount(page);
	int referenced = 0;
	int search_new_forks = 0;

	VM_BUG_ON(!PageKsm(page));
	VM_BUG_ON(!PageLocked(page));

	stable_node = page_stable_node(page);
	if (!stable_node)
		return 0;
again:
	hlist_for_each_entry(rmap_item, hlist, &stable_node->hlist, hlist) {
		struct anon_vma *anon_vma = rmap_item->anon_vma;
		struct vm_area_struct *vma;

		spin_lock(&anon_vma->lock);
		list_for_each_entry(vma, &anon_vma->head, anon_vma_node) {
			if (rmap_item->address < vma->vm_start ||
			    rmap_item->address >= vma->vm_end)
				continue;
			/*
			 * Initially we examine only the vma which covers this
			 * rmap_item; but later, if there is still work to do,
			 * we examine covering vmas in other mms: in case they
			 * were forked from the original since ksmd passed.
			 */
			if ((rmap_item->mm == vma->vm_mm) == search_new_forks)
				continue;

			if (memcg && !mm_match_cgroup(vma->vm_mm, memcg))
				continue;

			referenced += page_referenced_one(page, vma,
				rmap_item->address, &mapcount, vm_flags);
			if (!search_new_forks || !mapcount)
				break;
		}
		spin_unlock(&anon_vma->lock);
		if (!mapcount)
			goto out;
	}
	if (!search_new_forks++)
		goto again;
out:
	return referenced;
}

int try_to_unmap_ksm(struct page *page, enum ttu_flags flags)
{
	struct stable_node *stable_node;
	struct hlist_node *hlist;
	struct rmap_item *rmap_item;
	int ret = SWAP_AGAIN;
	int search_new_forks = 0;

	VM_BUG_ON(!PageKsm(page));
	VM_BUG_ON(!PageLocked(page));

	stable_node = page_stable_node(page);
	if (!stable_node)
		return SWAP_FAIL;
again:
	hlist_for_each_entry(rmap_item, hlist, &stable_node->hlist, hlist) {
		struct anon_vma *anon_vma = rmap_item->anon_vma;
		struct vm_area_struct *vma;

		spin_lock(&anon_vma->lock);
		list_for_each_entry(vma, &anon_vma->head, anon_vma_node) {
			if (rmap_item->address < vma->vm_start ||
			    rmap_item->address >= vma->vm_end)
				continue;
			/*
			 * Initially we examine only the vma which covers this
			 * rmap_item; but later, if there is still work to do,
			 * we examine covering vmas in other mms: in case they
			 * were forked from the original since ksmd passed.
			 */
			if ((rmap_item->mm == vma->vm_mm) == search_new_forks)
				continue;

			ret = try_to_unmap_one(page, vma,
					rmap_item->address, flags);
			if (ret != SWAP_AGAIN || !page_mapped(page)) {
				spin_unlock(&anon_vma->lock);
				goto out;
			}
		}
		spin_unlock(&anon_vma->lock);
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
	struct hlist_node *hlist;
	struct rmap_item *rmap_item;
	int ret = SWAP_AGAIN;
	int search_new_forks = 0;

	VM_BUG_ON(!PageKsm(page));
	VM_BUG_ON(!PageLocked(page));

	stable_node = page_stable_node(page);
	if (!stable_node)
		return ret;
again:
	hlist_for_each_entry(rmap_item, hlist, &stable_node->hlist, hlist) {
		struct anon_vma *anon_vma = rmap_item->anon_vma;
		struct vm_area_struct *vma;

		spin_lock(&anon_vma->lock);
		list_for_each_entry(vma, &anon_vma->head, anon_vma_node) {
			if (rmap_item->address < vma->vm_start ||
			    rmap_item->address >= vma->vm_end)
				continue;
			/*
			 * Initially we examine only the vma which covers this
			 * rmap_item; but later, if there is still work to do,
			 * we examine covering vmas in other mms: in case they
			 * were forked from the original since ksmd passed.
			 */
			if ((rmap_item->mm == vma->vm_mm) == search_new_forks)
				continue;

			ret = rmap_one(page, vma, rmap_item->address, arg);
			if (ret != SWAP_AGAIN) {
				spin_unlock(&anon_vma->lock);
				goto out;
			}
		}
		spin_unlock(&anon_vma->lock);
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

	for (node = rb_first(&root_stable_tree); node; node = rb_next(node)) {
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
			remove_node_from_stable_tree(stable_node);
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

static ssize_t sleep_mips_time_show(struct kobject *kobj,
				    struct kobj_attribute *attr, char *buf)
{
	return sprintf(buf, "%u\n", ksm_thread_sleep_mips_time);
}

static ssize_t sleep_mips_time_store(struct kobject *kobj,
				     struct kobj_attribute *attr,
				     const char *buf, size_t count)
{
	unsigned long nr_mips;
	int err;

	err = strict_strtoul(buf, 10, &nr_mips);
	if (err || nr_mips > UINT_MAX)
		return -EINVAL;

	ksm_thread_sleep_mips_time = nr_mips;

	return count;
}
KSM_ATTR(sleep_mips_time);

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


static ssize_t batch_millionth_ratio_show(struct kobject *kobj,
				  struct kobj_attribute *attr, char *buf)
{
	return sprintf(buf, "%u\n", ksm_batch_millionth_ratio);
}

static ssize_t batch_millionth_ratio_store(struct kobject *kobj,
				   struct kobj_attribute *attr,
				   const char *buf, size_t count)
{
	int err;
	unsigned long millionth_ratio;

	err = strict_strtoul(buf, 10, &millionth_ratio);
	if (err || millionth_ratio > UINT_MAX)
		return -EINVAL;

	ksm_batch_millionth_ratio = millionth_ratio;
	cal_ladder_pages_to_scan(ksm_pages_to_scan(ksm_batch_millionth_ratio));

	return count;
}
KSM_ATTR(batch_millionth_ratio);

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
	if (flags > KSM_RUN_UNMERGE)
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
		if (flags & KSM_RUN_UNMERGE) {
			current->flags |= PF_OOM_ORIGIN;
			err = unmerge_and_remove_all_rmap_items();
			current->flags &= ~PF_OOM_ORIGIN;
			if (err) {
				ksm_run = KSM_RUN_STOP;
				count = err;
			}
		}
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
	return sprintf(buf, "%lu\n", ksm_scan.seqnr);
}
KSM_ATTR_RO(full_scans);


static ssize_t enable_full_memory_scan_show(struct kobject *kobj,
				  struct kobj_attribute *attr, char *buf)
{
	return sprintf(buf, "%u\n", ksm_enable_full_scan);
}

/*
 * 0 -> 1: add all tasks' mm to ksm list
 * 1 -> 0: do the same like KSM_RUN_UNMERGE
 */
static ssize_t enable_full_memory_scan_store(struct kobject *kobj,
				   struct kobj_attribute *attr,
				   const char *buf, size_t count)
{
	int err;
	unsigned long enable_full_scan;

	err = strict_strtoul(buf, 10, &enable_full_scan);
	if (err || enable_full_scan > UINT_MAX)
		return -EINVAL;

	if (enable_full_scan == ksm_enable_full_scan)
		return count;

	ksm_enable_full_scan = enable_full_scan;

	if (!enable_full_scan) {
		mutex_lock(&ksm_thread_mutex);
		current->flags |= PF_OOM_ORIGIN;
		err = unmerge_and_remove_all_rmap_items();
		current->flags &= ~PF_OOM_ORIGIN;
		if (err) count = err;

		ksm_run = KSM_RUN_STOP;
		mutex_unlock(&ksm_thread_mutex);
	}

	return count;
}
KSM_ATTR(enable_full_memory_scan);


static struct attribute *ksm_attrs[] = {
	&sleep_mips_time_attr.attr,
	&batch_millionth_ratio_attr.attr,
	&run_attr.attr,
	&pages_shared_attr.attr,
	&pages_sharing_attr.attr,
	&pages_unshared_attr.attr,
	&pages_volatile_attr.attr,
	&full_scans_attr.attr,
	&enable_full_memory_scan_attr.attr,
	&min_scan_ratio_attr.attr,
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

	unsigned int pages_to_scan;

	pages_to_scan = ksm_pages_to_scan(ksm_batch_millionth_ratio);

	for (i = 0; i < ksm_scan_ladder_size; i++, mul *= 2) {
		ksm_scan_ladder[i].scan_ratio = ksm_min_scan_ratio * mul;
		ksm_scan_ladder[i].pages_to_scan = pages_to_scan
			* ksm_scan_ladder[i].scan_ratio / KSM_SCAN_RATIO_MAX;
		INIT_LIST_HEAD(&ksm_scan_ladder[i].vma_list);
		init_MUTEX(&ksm_scan_ladder[i].sem);
	}
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

	ksm_vma_table = kzalloc(sizeof(struct vm_area_struct *) *
				ksm_vma_table_size, GFP_KERNEL);

	if (!ksm_vma_table) {
		printk(KERN_ERR "ksm_vma_table allocation failed, size=%d\n",
		       ksm_vma_table_size);
		err = ENOMEM;
		goto out;
	}


#ifdef CONFIG_KSM_SHA1
	ksm_hash_tfm = crypto_alloc_hash("sha1", 0, CRYPTO_ALG_TYPE_SHASH);
	if (IS_ERR(ksm_hash_tfm)) {
		printk(KERN_ERR "Ksm failed to load transform SHA1\n");
		err = PTR_ERR(ksm_hash_tfm);
		goto out;
	}
#endif

	err = ksm_slab_init();
	if (err)
		goto out_free;

	err = mm_slots_hash_init();
	if (err)
		goto out_free1;

	ksm_thread = kthread_run(ksm_scan_thread, NULL, "ksmd");
	if (IS_ERR(ksm_thread)) {
		printk(KERN_ERR "ksm: creating kthread failed\n");
		err = PTR_ERR(ksm_thread);
		goto out_free2;
	}

#ifdef CONFIG_SYSFS
	err = sysfs_create_group(mm_kobj, &ksm_attr_group);
	if (err) {
		printk(KERN_ERR "ksm: register sysfs failed\n");
		kthread_stop(ksm_thread);
		goto out_free2;
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

out_free2:
	mm_slots_hash_free();
out_free1:
	ksm_slab_free();
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

