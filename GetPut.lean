import Std

/-!
Here we prove that the constraints enforced by ProveKit are satisfied IFF the
sequence of GetThenPut operations operate honestly on the memory.

In order to prove this statement, it is helpful to consider memory states beyond
those allowed by ProveKit. Specifically, the constraints enforced in ProveKit
ensure that the PUT timestamps for initialization are 0, and that the timestamp
for each subsequent PUT is its operation index plus 1. However, in the theorem
we prove here (`checks_iff_honest`), it is instead allowed that the
initialization timestamps are bounded by some `i`, and that the same `i` offset
the timestamps of the subsequent PUTs. This generalization facilitates the
proof, which successively processes the leading GetThenPut operation and
increments i. The statement we are interested in for ProveKit is the i=0 case.

Note that we work information theoretically, i.e. we compare multisets rather
than multiset hashes.

The addresses provided in a GetThenPut operation are permitted to be arbitrary
naturals - that they are in range of the permitted memory addresses is a
consequence of the theorem, not an assumption.
-/
namespace ProveKitRAM

abbrev ValueTime (V : Type) := V × Nat
abbrev AddrValueTime (V : Type) := Nat × ValueTime V

/-- A command supplies the address and the value to PUT. The GET claims an old pair. -/
structure GetThenPut (V : Type) where
  address : Nat
  reply : ValueTime V
  writtenValue : V

variable {K : Nat} {V : Type}

/-- Collect one AddrValueTime at each address from 0 through K−1, in order.
(Initialization and audit both use this). -/
def sweep (m : Fin K → ValueTime V) : List (AddrValueTime V) :=
  (List.finRange K).map fun a => (a.val, m a)

/-- Replace the value (or ValueTime, depending on usage) at address `a`. -/
def writeAt {α : Type} (m : Fin K → α) (a : Nat) (v : α) : Fin K → α :=
  fun b => if b.val = a then v else m b

/-- The AddrValueTimes for the PUTs of a List of GetThenPuts, where `i` is the
number of such already processed. -/
def putAVTs (i : Nat) : List (GetThenPut V) → List (AddrValueTime V)
  | [] => []
  | op :: ops => (op.address, (op.writtenValue, i + 1)) :: putAVTs (i + 1) ops

/-- The AddrValueTimes for the GETs of a List of GetThenPuts. This is
independent of the number of GetThenPuts already processed. -/
def getAVTs (ops: List (GetThenPut V)) : List (AddrValueTime V) :=
  ops.map fun op => (op.address, op.reply)

/-- The read time of each GetThenPut is at most its index (where `i` is the
number already processed) -/
def ReadTimesBounded (i : Nat) : List (GetThenPut V) → Prop
  | [] => True
  | op :: ops => op.reply.2 ≤ i ∧ ReadTimesBounded (i + 1) ops

/-- For all j, the jth read time is <= i+j and the multiset check passes.
(In the handwritten proof, this is predicate C_i) -/
def ProveKitAcceptsFrom (i : Nat) (m : Fin K → ValueTime V) (ops : List (GetThenPut V))
    (final : Fin K → ValueTime V) : Prop :=
  ReadTimesBounded i ops ∧
    (sweep m ++ putAVTs i ops).Perm (getAVTs ops ++ sweep final)

/-- The proposition "ProveKit accepts the witnesses", i.e. for all j, the jth
read time is <= j and the multiset check passes.  (In the handwritten proof,
this is predicate C, applied to a theta with i=0 and for which M(theta) holds) -/
def ProveKitAccepts (initial : Fin K → V) (ops : List (GetThenPut V)) (final : Fin K → ValueTime V) : Prop :=
  ProveKitAcceptsFrom 0 (fun a => (initial a, 0)) ops final

/-- Defn : a GetThenPut is "honest" if its address is in range and if the
ValueTime returned by the GET is equal to that currently stored by the memory
(This corresponds to E_1(theta) in the case where it is applied to the leading
GetThenPut in a sequence).  -/
def IsHonest (op : GetThenPut V) (m : Fin K → ValueTime V) :=
  ∃ h : op.address < K, m ⟨op.address, h⟩ = op.reply

/-- The List of GetThenPuts honestly develops the initial memory `m` into the
final memory  `final`, where the timestamps are offset by `i`. In the
handwritten notes, this is the predicate H(theta). -/
def HonestFrom (i : Nat) (m : Fin K → ValueTime V) : List (GetThenPut V) → (Fin K → ValueTime V) → Prop
  | [], final => m = final
  | op :: ops, final =>
    IsHonest op m ∧
      HonestFrom (i + 1) (writeAt m op.address (op.writtenValue, i + 1)) ops final

private theorem mem_sweep (m : Fin K → ValueTime V) (a : Nat) (c : ValueTime V) :
    (a, c) ∈ sweep m ↔ ∃ h : a < K, m ⟨a, h⟩ = c := by
  simp [sweep, Fin.exists_iff]

/-- All PUTs still to come have timestamps strictly greater than `i`. -/
private theorem later_puts (i : Nat) (ops : List (GetThenPut V)) (x : AddrValueTime V)
    (hx : x ∈ putAVTs i ops) : i < x.2.2 := by
  induction ops generalizing i with
  | nil => simp [putAVTs] at hx
  | cons op ops ih =>
    rcases List.mem_cons.mp hx with rfl | tail
    · exact Nat.lt_succ_self _
    · exact Nat.lt_trans (Nat.lt_succ_self _) (ih _ tail)

/-- This is the multiset identity used in proposition B in the handwritten
notes, where it plays the crucial role in relating C_ms(theta) to C_ms(theta').
It says that adding the AVT of the next PUT to the current memory sweep yields
the same multiset as updating the current memory with that PUT, then sweeping,
then adding the corresponding GET to the result.  -/
private theorem exchange (m : Fin K → ValueTime V) (a : Fin K) (newCell : ValueTime V) :
    ((a.val, newCell) :: sweep m).Perm
      ((a.val, m a) :: sweep (writeAt m a.val newCell)) := by
  let rest := (List.finRange K).erase a
  have split (table : Fin K → ValueTime V) : (sweep table).Perm
      ((a.val, table a) :: rest.map (fun b => (b.val, table b))) :=
    (List.perm_cons_erase (List.mem_finRange a)).map (fun (b : Fin K) => (b.val, table b))
  have unchanged : rest.map (fun b => (b.val, writeAt m a.val newCell b)) =
      rest.map (fun b => (b.val, m b)) := by
    apply List.map_congr_left
    intro b hb
    have ne := ((List.nodup_finRange K).mem_erase_iff.mp hb).1
    have different : b.val ≠ a.val := fun eq => ne (Fin.ext eq)
    simp [writeAt, different]
  have after := split (writeAt m a.val newCell)
  have atAddress : writeAt m a.val newCell a = newCell := by simp [writeAt]
  rw [atAddress, unchanged] at after
  exact (((split m).cons _).trans (.swap _ _ _)).trans (after.symm.cons _)

/-- This is the theorem from the handwritten notes, where the Prop `bound`
corresponds to M(theta). Applied to theta = (m, ops, final, i) that arise in
ProveKit (so i=0), it is precisely the statement that the constraints enforced
by ProveKit are satisfied IFF the GetThenPuts honestly develop the initial
memory state `m` into the final memory state `final`.  -/
theorem checks_iff_honest (i : Nat) (m : Fin K → ValueTime V) (ops : List (GetThenPut V))
    (final : Fin K → ValueTime V) (bound : ∀ a, (m a).2 ≤ i) :
    ProveKitAcceptsFrom i m ops final ↔ HonestFrom i m ops final := by
  induction ops generalizing i m with
  | nil =>
    simp only [ProveKitAcceptsFrom, ReadTimesBounded, putAVTs, List.append_nil, true_and, HonestFrom]
    constructor
    · intro perm
      funext a
      have member := perm.mem_iff.mpr ((mem_sweep final a.val (final a)).mpr ⟨a.isLt, rfl⟩)
      exact ((mem_sweep m a.val (final a)).mp member).choose_spec
    · rintro rfl
      exact .refl _
  | cons op ops ih =>
    let next := writeAt m op.address (op.writtenValue, i + 1)
    have nextBound (a : Fin K) : (next a).2 ≤ i + 1 := by
      simp only [next, writeAt]
      split
      · exact Nat.le_refl _
      · exact Nat.le_succ_of_le (bound a)
    -- Once the GET matches the table, cancelling it leaves precisely the suffix check.
    have cancel (h : op.address < K) (matchGET : m ⟨op.address, h⟩ = op.reply) :
        ProveKitAcceptsFrom i m (op :: ops) final ↔ ProveKitAcceptsFrom (i + 1) next ops final := by
      have time := bound ⟨op.address, h⟩
      rw [matchGET] at time
      have move := (exchange m ⟨op.address, h⟩ (op.writtenValue, i + 1)).append_right (putAVTs (i + 1) ops)
      simp only [List.cons_append, matchGET] at move
      simp only [ProveKitAcceptsFrom, ReadTimesBounded, time, true_and, putAVTs]
      apply and_congr_right
      intro _
      have rearrange := List.perm_middle.trans move
      exact ⟨fun p => (rearrange.symm.trans p).cons_inv, fun p => rearrange.trans (p.cons _)⟩
    constructor
    · intro accepted
      have member := accepted.2.mem_iff.mpr List.mem_cons_self
      rcases List.mem_append.mp member with old | future
      · obtain ⟨h, eq⟩ := (mem_sweep _ _ _).mp old
        exact ⟨⟨h, eq⟩, (ih _ next nextBound).mp ((cancel h eq).mp accepted)⟩
      · exact (Nat.not_lt_of_ge accepted.1.1 (later_puts i (op :: ops) _ future)).elim
    · rintro ⟨⟨h, eq⟩, tail⟩
      exact (cancel h eq).mpr ((ih _ next nextBound).mpr tail)

end ProveKitRAM
