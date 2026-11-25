# Soundness and correctness of ProveKit’s Spice RAM argument

We show here that for given initial values and list of load and store commands (which include the
claimed value returned), the commands are honest w.r.t. the initial values iff
they can be extended to a witness that satisfies the ProveKit constraints.  This
is the content of theorem `correct_iff_provekit_witnesses_exist` in
[LoadStore.lean](LoadStore.lean). The proof ultimately reduces to proving an
analogous statement concerning GetThenPuts - this is theorem `checks_iff_honest`
in [GetPut.lean](GetPut.lean).

Note that we work information theoretically, i.e. we compare multisets rather
than multiset hashes.

The addresses provided in Loads and Stores are permitted to be arbitrary
naturals - that they are in range of the permitted memory addresses is a
consequence of the theorem, not an assumption.

Run `lake build` with the pinned Lean toolchain. The model follows the RAM
compiler at commit `6a5cd629`. [ProveKit
source](https://github.com/worldfnd/provekit/blob/6a5cd6293800b6818d1f4986b29509e46d05e608/provekit/r1cs-compiler/src/memory/ram.rs)
