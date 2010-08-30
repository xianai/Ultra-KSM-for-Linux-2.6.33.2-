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
/**
 * struct mm_slot - ksm information per mm that is being scanned
 * @link: link to the mm_slots hash list
 * @mm_list: link into the mm_slots list, rooted in ksm_mm_head
 * @rmap_list: head for this mm_slot's singly-linked list of rmap_items
 * @mm: the mm that this information is valid for
 */
struct mm_slot {
	struct hlist_node link;
	struct list_head mm_list;
	struct rmap_item *rmap_list;
	struct mm_struct *mm;
};

int __ksm_enter(struct mm_struct *mm);
void __ksm_exit(struct mm_struct *mm);
int ksm_fork(struct mm_struct *mm, struct mm_struct *oldmm);

static inline void ksm_exit(struct mm_struct *mm)
{
	if (test_bit(MMF_VM_MERGEABLE, &mm->flags))
		__ksm_exit(mm);
}

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

static inline void ksm_init_vma(struct vm_area_struct *vma)
{
	vma->dedup_ratio = 0;
	vma->ksm_index = -1;
	INIT_LIST_HEAD(&vma->ksm_list);
	vma->pages_scanned = 0;
	vma->pages_to_scan = 0;
	vma->rung = 0;
	vma->rmap_list = NULL;
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
	spinlock_t vma_list_lock;
	struct semaphore sem;
	struct list_head *current_scan;
	unsigned int pages_to_scan;
	unsigned char round_finished;
	unsigned long scan_ratio;
};

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
