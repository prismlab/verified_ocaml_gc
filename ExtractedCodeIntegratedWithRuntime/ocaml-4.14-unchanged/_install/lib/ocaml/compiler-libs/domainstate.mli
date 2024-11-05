# 0 "utils/domainstate.mli.c"
# 0 "<built-in>"
# 0 "<command-line>"
# 1 "/usr/include/stdc-predef.h" 1 3 4
# 0 "<command-line>" 2
# 1 "utils/domainstate.mli.c"
# 17 "utils/domainstate.mli.c"
type t =

# 1 "runtime/caml/domain_state.tbl" 1
# 17 "runtime/caml/domain_state.tbl"
| Domain_young_limit
| Domain_young_ptr


| Domain_exception_pointer


| Domain_young_base
| Domain_young_start
| Domain_young_end
| Domain_young_alloc_start
| Domain_young_alloc_end
| Domain_young_alloc_mid
| Domain_young_trigger
| Domain_minor_heap_wsz
| Domain_in_minor_collection
| Domain_extra_heap_resources_minor
| Domain_ref_table
| Domain_ephe_ref_table
| Domain_custom_table


| Domain_mark_stack


| Domain_stack_low
| Domain_stack_high
| Domain_stack_threshold
| Domain_extern_sp
| Domain_trapsp
| Domain_trap_barrier
| Domain_external_raise
| Domain_exn_bucket


| Domain_top_of_stack
| Domain_bottom_of_stack
| Domain_last_return_address
| Domain_gc_regs


| Domain_backtrace_active
| Domain_backtrace_pos
| Domain_backtrace_buffer
| Domain_backtrace_last_exn


| Domain_compare_unordered
| Domain_requested_major_slice
| Domain_requested_minor_gc
| Domain_local_roots

| Domain_stat_minor_words
| Domain_stat_promoted_words
| Domain_stat_major_words
| Domain_stat_minor_collections
| Domain_stat_major_collections
| Domain_stat_heap_wsz
| Domain_stat_top_heap_wsz
| Domain_stat_compactions
| Domain_stat_forced_major_collections
| Domain_stat_heap_chunks


| Domain_eventlog_startup_timestamp
| Domain_eventlog_startup_pid
| Domain_eventlog_paused
| Domain_eventlog_enabled
| Domain_eventlog_out







| Domain_extra_params
# 20 "utils/domainstate.mli.c" 2


val idx_of_field : t -> int
