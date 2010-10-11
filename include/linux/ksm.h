#ifndef __LINUX_KSM_H
#define __LINUX_KSM_H
/*
 * Memory merging support.
 *
 * This code enables dynamic sharing of identical pages found in different
 * memory areas, even if they are not shared by fork().
 */

#include <linux/bitops.h>
#include <linux/mm.h>
#include <linux/pagemap.h>
#include <linux/rmap.h>
#include <linux/sched.h>

struct stable_node;
struct mem_cgroup;

#ifdef CONFIG_KSM
void __ksm_enter(struct mm_struct *mm);
void __ksm_exit(struct mm_struct *mm);
int ksm_fork(struct mm_struct *mm, struct mm_struct *oldmm);


/*
 * A KSM page is one of those write-protected "shared pages" or "merged pages"
 * which KSM maps into multiple mms, wherever identical anonymous page content
 * is found in VM_MERGEABLE vmas.  It's a PageAnon page, pointing not to any
 * anon_vma, but to that page's node of the stable tree.
 */
static inline int PageKsm(struct page *page)
{
	return ((unsigned long)page->mapping & PAGE_MAPPING_FLAGS) ==
				(PAGE_MAPPING_ANON | PAGE_MAPPING_KSM);
}

static inline struct stable_node *page_stable_node(struct page *page)
{
	return PageKsm(page) ? page_rmapping(page) : NULL;
}

static inline void set_page_stable_node(struct page *page,
					struct stable_node *stable_node)
{
	page->mapping = (void *)stable_node +
				(PAGE_MAPPING_ANON | PAGE_MAPPING_KSM);
}

/* must be done before linked to mm */
static inline void ksm_init_vma(struct vm_area_struct *vma)
{
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
}

void ksm_remove_vma(struct vm_area_struct *vma);

/*
 * When do_swap_page() first faults in from swap what used to be a KSM page,
 * no problem, it will be assigned to this vma's anon_vma; but thereafter,
 * it might be faulted into a different anon_vma (or perhaps to a different
 * offset in the same anon_vma).  do_swap_page() cannot do all the locking
 * needed to reconstitute a cross-anon_vma KSM page: for now it has to make
 * a copy, and leave remerging the pages to a later pass of ksmd.
 *
 * We'd like to make this conditional on vma->vm_flags & VM_MERGEABLE,
 * but what if the vma was unmerged while the page was swapped out?
 */
struct page *ksm_does_need_to_copy(struct page *page,
			struct vm_area_struct *vma, unsigned long address);
static inline struct page *ksm_might_need_to_copy(struct page *page,
			struct vm_area_struct *vma, unsigned long address)
{
	struct anon_vma *anon_vma = page_anon_vma(page);

	if (!anon_vma ||
	    (anon_vma == vma->anon_vma &&
	     page->index == linear_page_index(vma, address)))
		return page;

	return ksm_does_need_to_copy(page, vma, address);
}

int page_referenced_ksm(struct page *page,
			struct mem_cgroup *memcg, unsigned long *vm_flags);
int try_to_unmap_ksm(struct page *page, enum ttu_flags flags);
int rmap_walk_ksm(struct page *page, int (*rmap_one)(struct page *,
		  struct vm_area_struct *, unsigned long, void *), void *arg);
void ksm_migrate_page(struct page *newpage, struct page *oldpage);

struct scan_rung {
	struct list_head vma_list;
	//spinlock_t vma_list_lock;
	//struct semaphore sem;
	struct list_head *current_scan;
	unsigned int pages_to_scan;
	unsigned char round_finished; /* rung is ready for the next round */
	unsigned char fully_scanned;
	unsigned long scan_ratio;
	unsigned long vma_num;
	//unsigned long vma_finished;
	unsigned long scan_turn;
};

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

struct ksm_checksum {
	u32 sample_num;
	u32 val;
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
	struct ksm_checksum checksum;
	struct vm_area_struct *old_vma;
};

/**
 * struct node_vma - group rmap_items linked in a same stable
 * node together.
 */
struct node_vma {
	union {
		struct vm_area_struct *vma;
		unsigned long key;  /* vma is used as key sorted on hlist */
	};
	struct hlist_node hlist;
	struct hlist_head rmap_hlist;
	struct stable_node *head;
	unsigned long last_update;
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
	struct anon_vma *anon_vma;	/* when stable */
	struct vm_area_struct *vma;
	unsigned long address;	/* + low bits used for flags below */
	/* Appendded to (un)stable tree on which scan round */
	unsigned long append_round;

	/* Which rung scan turn it was last scanned */
	//unsigned long last_scan;
	unsigned long entry_index;
	struct ksm_checksum oldchecksum;	/* when unstable */
	union {
		struct rb_node node;	/* when node of unstable tree */
		struct {		/* when listed from stable tree's node_vma */
			struct node_vma *head;
			struct hlist_node hlist;
		};
	};
} __attribute__((aligned(4)));

struct rmap_list_entry {
	union {
		struct rmap_item *item;
		unsigned long addr;
	};
	// lowest bit is used for is_addr tag
	//unsigned char is_addr;
} __attribute__((aligned(4))); // 4 aligned to fit in to pages



//extern struct semaphore ksm_scan_sem;
#else  /* !CONFIG_KSM */

static inline int ksm_fork(struct mm_struct *mm, struct mm_struct *oldmm)
{
	return 0;
}

static inline void ksm_exit(struct mm_struct *mm)
{
}

static inline int PageKsm(struct page *page)
{
	return 0;
}

#ifdef CONFIG_MMU

static inline struct page *ksm_might_need_to_copy(struct page *page,
			struct vm_area_struct *vma, unsigned long address)
{
	return page;
}

static inline int page_referenced_ksm(struct page *page,
			struct mem_cgroup *memcg, unsigned long *vm_flags)
{
	return 0;
}

static inline int try_to_unmap_ksm(struct page *page, enum ttu_flags flags)
{
	return 0;
}

static inline int rmap_walk_ksm(struct page *page, int (*rmap_one)(struct page*,
		struct vm_area_struct *, unsigned long, void *), void *arg)
{
	return 0;
}

static inline void ksm_migrate_page(struct page *newpage, struct page *oldpage)
{
}
#endif /* CONFIG_MMU */
#endif /* !CONFIG_KSM */

#endif /* __LINUX_KSM_H */
