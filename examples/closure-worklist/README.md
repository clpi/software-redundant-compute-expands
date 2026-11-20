# Incremental closure for a fixed canonical view

The source remains the append-only record log. `Worklist` is a rebuildable
index for the positive, filtered `Canon.viewC` at one fixed projection level,
lift chain and pure color predicate. A record with level above the view or
rejected by the predicate cannot fire. A change to these parameters (or a
withdrawal that changes which records are admitted) requires a new view or an
independently checked retraction algorithm; it is not a positive append.

Projected rule keys retain the ordered premise tuple, including duplicates.
Rules with identical projected pairs share a waiter count without dropping
any source records. Readiness uses **distinct** missing projected terms,
because `Canon.Derives.step` checks membership, not multiplicity. Projection
may identify distinct source terms. This is not permission to collapse
ordered instructions, proof terms, effects or obligation identities.

At each drained append prefix the invariant is:

1. Every derived term has a finite derivation from admitted records.
2. A rule's remaining count is the cardinality of its missing premise
   set; the reverse index enumerates exactly its outstanding memberships.
3. All registered zero-count heads are in the derived set.

Registration happens against the drained previous state before firing any
new rule. During drain, the count is indexed against processed terms; a term
is discovered and queued once. As each newly processed term consumes its
waiters, old incomplete rules can fire without rescanning the rule set.
Soundness comes from firing only ready rules. When the queue drains, the
result is closed under every admitted rule; leastness implies completeness.
Unsupported cycles are not seeded.

Run `python3 -B replay.py | cmp - replay.json` for synthetic controls and
1,920 growing oracle comparisons under three resolution levels. Counts
are operations, not runtime. New edge registrations, waiter visits and term
pops are reported separately; the cold oracle is a synchronous full scan on
each prefix, not the strongest alternate implementation. The Python worklist
is an executable reference, not a verified compiler implementation or a
machine-checked refinement of the Lean model.
