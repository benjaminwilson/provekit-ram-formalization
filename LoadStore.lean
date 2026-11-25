import GetPut

/-! Soundness and completeness for program loads and stores. -/
namespace ProveKitRAM.Semantics

variable {K : Nat} {V : Type}

/-- The operations permitted on the public interface to the checker: load and
store, where a load holds also the value that was returned.  Note that
load/store are timestamp agnostic (since they are public interface). -/
inductive LoadOrStore (V : Type) where
  | load (address : Nat) (value : V)
  | store (address : Nat) (value : V)

/-- Prop: the provided sequence of LoadOrStores are honest when played forward
starting from the provided current reference memory, i.e. the address of every
LoadOrStore is in range, each load returns the value that was most recently
stored at that address (which is determined by fetching it from the current
reference memory `memory`). -/
def AreHonest (memory : Fin K → V) : List (LoadOrStore V) → Prop
  | [] => True
  | .load a v :: cs => (∃ h : a < K, memory ⟨a, h⟩ = v) ∧ AreHonest memory cs
  | .store a v :: cs => a < K ∧ AreHonest (writeAt memory a v) cs

/-- This type defines the shape of the extra witnesses required to fully specify
GetThenPuts corresponding to given LoadOrStores.  Each LoadOrStore already
supplies the address and value to PUT.  The extras: In the case of a load, only
its read time; while in the case of a store, the old value and the read time are
required.
-/
inductive Witnesses : List (LoadOrStore V) → Type where
  | nil : Witnesses []
  | load {a v cs} (time : Nat) (_tail : Witnesses cs) : Witnesses (.load a v :: cs)
  | store {a v cs} (old : ValueTime V) (_tail : Witnesses cs) : Witnesses (.store a v :: cs)

/-- Construct the GetThenPuts from the Witnesses (which knows its original
LoadOrStore list via its type). -/
def Witnesses.getThenPuts {cs : List (LoadOrStore V)} : Witnesses cs → List (GetThenPut V)
  | .nil => []
  | .load (a := a) (v := v) time tail => ⟨a, (v, time), v⟩ :: tail.getThenPuts
  | .store (a := a) (v := v) old tail => ⟨a, old, v⟩ :: tail.getThenPuts

/-- For any reference memory `memory`, timestamp table `times`, and starting
index `i`, the loads and stores `cs` form an honest continuation from `memory`
IFF there exist witnesses `ws` completing `cs` and a final value-and-timestamp
table `final` such that `ws.getThenPuts` forms an honest GET/PUT continuation
from `zip(memory, times)`, starting at index `i` and ending in `final`. -/
private theorem honest_witnesses (memory : Fin K → V) (times : Fin K → Nat)
    (i : Nat) (cs : List (LoadOrStore V)) :
    AreHonest memory cs ↔ ∃ ws : Witnesses cs, ∃ final,
      HonestFrom i (fun a => (memory a, times a)) ws.getThenPuts final := by
  induction cs generalizing memory times i with
  | nil =>
    exact ⟨fun _ => ⟨.nil, _, rfl⟩, fun _ => True.intro⟩
  | cons c cs ih =>
    have writePair (a : Nat) (v : V) :
        (fun b => (writeAt memory a v b, writeAt times a (i + 1) b)) =
          writeAt (fun b => (memory b, times b)) a (v, i + 1) := by
      funext b
      by_cases h : b.val = a <;> simp [writeAt, h]
    have afterPut (a : Nat) (v : V) := ih (writeAt memory a v) (writeAt times a (i + 1)) (i + 1)
    simp only [writePair] at afterPut
    cases c with
    | load a v =>
      have refresh (h : a < K) (hv : memory ⟨a, h⟩ = v) : writeAt memory a v = memory := by
        funext b
        by_cases eq : b.val = a
        · obtain rfl : b = ⟨a, h⟩ := Fin.ext eq
          simp [writeAt, hv]
        · simp [writeAt, eq]
      constructor
      · rintro ⟨⟨h, hv⟩, tail⟩
        rw [← refresh h hv] at tail
        obtain ⟨ws, final, honest⟩ := (afterPut a v).mp tail
        exact ⟨.load (times ⟨a, h⟩) ws, final, ⟨h, Prod.ext hv rfl⟩, honest⟩
      · rintro ⟨ws, final, honest⟩
        cases ws with
        | load time tail =>
          obtain ⟨⟨h, pair⟩, rest⟩ := honest
          have hv := congrArg Prod.fst pair
          exact ⟨⟨h, hv⟩, (refresh h hv) ▸ (afterPut a v).mpr ⟨tail, final, rest⟩⟩
    | store a v =>
      constructor
      · rintro ⟨h, tail⟩
        obtain ⟨ws, final, honest⟩ := (afterPut a v).mp tail
        exact ⟨.store (memory ⟨a, h⟩, times ⟨a, h⟩) ws, final, ⟨h, rfl⟩, honest⟩
      · rintro ⟨ws, final, honest⟩
        cases ws with
        | store old tail =>
          exact ⟨honest.1.choose, (afterPut a v).mpr ⟨tail, final, honest.2⟩⟩

/-- For given initial values and list of load and store commands (which include claimed
load results), the commands are honest w.r.t. the initial values iff there exist
witnesses of the corresponding shape that satisfy the ProveKit constraints. -/
theorem correct_iff_provekit_witnesses_exist (initial : Fin K → V) (commands : List (LoadOrStore V)) :
    AreHonest initial commands ↔
      ∃ ws : Witnesses commands, ∃ final : Fin K → ValueTime V, ProveKitAccepts initial ws.getThenPuts final := by
  simp only [ProveKitAccepts, checks_iff_honest 0 (fun a => (initial a, 0)) _ _ (fun _ => Nat.le_refl 0)]
  exact honest_witnesses initial (fun _ => 0) 0 commands

end ProveKitRAM.Semantics
