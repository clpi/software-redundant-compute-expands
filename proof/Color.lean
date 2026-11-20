/-
  Append-only coloring of uniquely witnessed configurations,
  with reweightable parameters.

  A configuration is any item of an append-only stream: a
  node, a hyperedge, a symbol record. A color is a structural
  key of a configuration (for hyperedges, an edge signature);
  the stream of colors is a list of naturals. The painting of
  a stream marks every position with its color and a flag: the
  flag is set exactly at the first occurrence of the color,
  the color's unique witness, and clear at every later
  occurrence, a redundant realization.

  Proved here: the painting of an appended stream is the
  painting of the old stream followed by the painting of the
  new part against what was seen (nothing already painted is
  ever repainted); every color present has exactly one
  witness; witnesses count the distinct colors and redundant
  marks count the measure; the incremental run over an
  appended stream equals the from-scratch run.

  Weights are parameters on colors, chosen and changed on the
  fly. The weighted measure is the sum of weights over
  redundant marks. The painting does not read the weights, so
  reweighting changes values and never the painting; the
  weighted measure is additive and homogeneous in the weights,
  monotone under expansion, invariant under re-listing,
  superadditive over joins with one further weight per shared
  color, and it splits exactly as total weight minus witness
  weight. The witness set is a cheapest cover of the stream's
  colors under every weighting at once, so the redundant
  weight is exactly the largest saving any deduplication can
  make, for every weighting simultaneously.
-/

import Relist

namespace Redundant

/-- The weighted counter: scanning with a seen list, each
    element already seen adds its weight. -/
def wa (w : Nat → Nat) : List Nat → List Nat → Nat
  | _, [] => 0
  | seen, x :: xs => (if x ∈ seen then w x else 0) + wa w (x :: seen) xs

/-- The weighted measure of a stream of colors. -/
def wred (w : Nat → Nat) (l : List Nat) : Nat := wa w [] l

/-- Total weight of a list. -/
def wsum (w : Nat → Nat) (l : List Nat) : Nat := (l.map w).sum

/-- The painting: every position gets its color and a flag,
    set exactly at the color's first occurrence. -/
def paint : List Nat → List Nat → List (Nat × Bool)
  | _, [] => []
  | seen, x :: xs => (x, decide (x ∉ seen)) :: paint (x :: seen) xs

namespace Color

/-- Unit weights recover the counter. -/
theorem unit : ∀ (seen l : List Nat), wa (fun _ => 1) seen l = aux seen l := by
  intro seen l
  induction l generalizing seen with
  | nil => rfl
  | cons x xs ih => simp only [wa, aux, ih]

/-- Unit weights recover the measure. -/
theorem unit_red (l : List Nat) : wred (fun _ => 1) l = red l := unit [] l

theorem append (w : Nat → Nat) (seen a b : List Nat) :
    wa w seen (a ++ b) = wa w seen a + wa w (a.reverse ++ seen) b := by
  induction a generalizing seen with
  | nil => simp [wa]
  | cons x xs ih =>
    simp only [List.cons_append, wa, List.reverse_cons]
    rw [ih, List.append_assoc]
    ac_rfl

theorem mono (w : Nat → Nat) {s s' : List Nat} (h : ∀ x ∈ s, x ∈ s')
    (l : List Nat) : wa w s l ≤ wa w s' l := by
  induction l generalizing s s' with
  | nil => simp [wa]
  | cons x xs ih =>
    have h' : ∀ y ∈ x :: s, y ∈ x :: s' := by
      intro y hy
      cases List.mem_cons.mp hy with
      | inl he => subst he; exact List.mem_cons.mpr (Or.inl rfl)
      | inr he => exact List.mem_cons_of_mem x (h y he)
    have hih := ih h'
    simp only [wa]
    by_cases hx : x ∈ s
    · simp [hx, h x hx]; omega
    · by_cases hx' : x ∈ s'
      · simp [hx, hx']; omega
      · simp [hx, hx']; exact hih

theorem congr (w : Nat → Nat) {s s' : List Nat} (h : ∀ x, x ∈ s ↔ x ∈ s')
    (l : List Nat) : wa w s l = wa w s' l :=
  Nat.le_antisymm (mono w (fun x hx => (h x).mp hx) l)
    (mono w (fun x hx => (h x).mpr hx) l)

/-- Reweighting is additive: the weighted measure under a sum
    of weightings is the sum of the weighted measures. -/
theorem add (w v : Nat → Nat) : ∀ (seen l : List Nat),
    wa (fun x => w x + v x) seen l = wa w seen l + wa v seen l := by
  intro seen l
  induction l generalizing seen with
  | nil => rfl
  | cons x xs ih =>
    simp only [wa, ih]
    by_cases hx : x ∈ seen <;> simp [hx] <;> omega

/-- Reweighting is homogeneous: scaling every weight scales
    the weighted measure. -/
theorem scale (c : Nat) (w : Nat → Nat) : ∀ (seen l : List Nat),
    wa (fun x => c * w x) seen l = c * wa w seen l := by
  intro seen l
  induction l generalizing seen with
  | nil => simp [wa]
  | cons x xs ih =>
    simp only [wa, ih]
    by_cases hx : x ∈ seen <;> simp [hx, Nat.mul_add]

/-- Raising weights never lowers the weighted measure. -/
theorem wmono {w v : Nat → Nat} (h : ∀ x, w x ≤ v x) : ∀ (seen l : List Nat),
    wa w seen l ≤ wa v seen l := by
  intro seen l
  induction l generalizing seen with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    simp only [wa]
    have := ih (x :: seen)
    have hx := h x
    by_cases hs : x ∈ seen <;> simp [hs] <;> omega

/-- The weighted counter is invariant under every permutation
    of the stream. -/
theorem perm (w : Nat → Nat) {l₁ l₂ : List Nat} (p : l₁.Perm l₂) :
    ∀ seen, wa w seen l₁ = wa w seen l₂ := by
  induction p with
  | nil => intro _; rfl
  | cons x _ ih => intro seen; simp only [wa]; rw [ih]
  | swap x y l =>
    intro seen
    simp only [wa]
    have hc : wa w (x :: y :: seen) l = wa w (y :: x :: seen) l :=
      congr w (fun z => by
        simp only [List.mem_cons]
        constructor
        · rintro (h | h | h)
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · rintro (h | h | h)
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)) l
    rw [hc]
    by_cases hx : x ∈ seen <;> by_cases hy : y ∈ seen <;>
      by_cases hxy : x = y <;> simp_all <;> omega
  | trans _ _ ih₁ ih₂ => intro seen; rw [ih₁, ih₂]

/-- A seen color occurring in the stream adds at least its
    weight. -/
theorem pos (w : Nat → Nat) {x : Nat} : ∀ (seen l : List Nat),
    x ∈ seen → x ∈ l → w x ≤ wa w seen l := by
  intro seen l
  induction l generalizing seen with
  | nil => intro _ h; simp at h
  | cons y ys ih =>
    intro hseen h
    simp only [wa]
    cases List.mem_cons.mp h with
    | inl he => subst he; rw [if_pos hseen]; omega
    | inr he =>
      have := ih _ (List.mem_cons_of_mem y hseen) he
      omega

/-- Monotone under append on the right. -/
theorem left (w : Nat → Nat) (a b : List Nat) : wred w a ≤ wred w (a ++ b) := by
  simp only [wred]
  rw [append]
  omega

/-- Superadditive over joins, under every weighting. -/
theorem sum (w : Nat → Nat) (a b : List Nat) :
    wred w a + wred w b ≤ wred w (a ++ b) := by
  simp only [wred]
  rw [append]
  have := mono w (s := []) (s' := a.reverse ++ []) (fun x hx => by simp at hx) b
  omega

/-- A color shared by the two parts adds at least its weight
    beyond the sum, under every weighting. -/
theorem strict (w : Nat → Nat) {x : Nat} {a b : List Nat}
    (ha : x ∈ a) (hb : x ∈ b) :
    wred w a + wred w b + w x ≤ wred w (a ++ b) := by
  obtain ⟨s, t, rfl, hxnot⟩ := Split.first b hb
  simp only [wred]
  rw [append w [] a (s ++ x :: t), append w (a.reverse ++ []) s (x :: t),
    append w [] s (x :: t)]
  simp only [wa]
  have hxin : x ∈ s.reverse ++ (a.reverse ++ []) := by simp [ha]
  have hxout : x ∉ s.reverse ++ [] := by simp [hxnot]
  rw [if_pos hxin, if_neg hxout]
  have m1 := mono w (s := []) (s' := a.reverse ++ []) (fun y hy => by simp at hy) s
  have m2 := mono w (s := x :: (s.reverse ++ [])) (s' := x :: (s.reverse ++ (a.reverse ++ [])))
    (fun y hy => by
      simp only [List.mem_cons, List.mem_append, List.mem_reverse,
        List.not_mem_nil, or_false] at hy ⊢
      rcases hy with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)) t
  omega

/-- Witness weight plus redundant weight is total weight: the
    exact split under every weighting. -/
theorem split (w : Nat → Nat) : ∀ l : List Nat, wred w l + wsum w (uniq l) = wsum w l := by
  have key : ∀ (l seen : List Nat), wa w seen l
      = wsum w ((uniq l).filter (fun v => decide (v ∈ seen))) + (wsum w l - wsum w (uniq l))
        ∧ wsum w (uniq l) ≤ wsum w l := by
    intro l
    induction l with
    | nil => intro _; simp [wa, wsum, uniq]
    | cons x xs ih =>
      intro seen
      have hmem := Uniq.mem (a := x) xs
      have hnd := Uniq.nodup xs
      obtain ⟨e1, b1⟩ := ih (x :: seen)
      obtain ⟨_, _⟩ := ih seen
      -- weight of the distinct colors of xs already seen, with x added
      have hf : ∀ U : List Nat, U.Nodup →
          wsum w (U.filter (fun v => decide (v ∈ x :: seen)))
            = wsum w (U.filter (fun v => decide (v ∈ seen)))
              + (if x ∈ U ∧ x ∉ seen then w x else 0) := by
        intro U
        induction U with
        | nil => intro _; simp [wsum]
        | cons u us ihu =>
          intro hu
          have hu1 : u ∉ us := (List.nodup_cons.mp hu).1
          have hih := ihu (List.nodup_cons.mp hu).2
          by_cases hux : u = x
          · subst hux
            have hc : us.filter (fun v => decide (v ∈ u :: seen))
                = us.filter (fun v => decide (v ∈ seen)) :=
              List.filter_congr (fun v hv => by
                have hvu : v ≠ u := fun h => hu1 (h ▸ hv)
                simp [hvu])
            have hp : decide (u ∈ u :: seen) = true := by simp
            rw [List.filter_cons_of_pos (p := fun v => decide (v ∈ u :: seen)) hp, hc]
            by_cases hs : u ∈ seen
            · have hq : decide (u ∈ seen) = true := by simp [hs]
              rw [List.filter_cons_of_pos (p := fun v => decide (v ∈ seen)) hq]
              simp [hs, wsum]
            · have hq : ¬ decide (u ∈ seen) = true := by simp [hs]
              rw [List.filter_cons_of_neg (p := fun v => decide (v ∈ seen)) hq]
              simp [hs, wsum]; omega
          · simp only [wsum] at hih ⊢
            by_cases hs : u ∈ seen
            · simp [List.filter_cons, hs, hux, hih]
              by_cases hx : x ∈ us <;> by_cases hxs : x ∈ seen <;>
                simp_all <;> omega
            · simp [List.filter_cons, hs, hux, hih]
              by_cases hx : x ∈ us <;> by_cases hxs : x ∈ seen <;>
                simp_all <;> omega
      have hwa : wa w seen (x :: xs) = (if x ∈ seen then w x else 0) + wa w (x :: seen) xs := rfl
      rw [hwa, e1, hf _ hnd]
      simp only [uniq]
      by_cases hx : x ∈ xs
      · rw [if_pos hx]
        have hle : w x ≤ wsum w xs - wsum w (uniq xs) + w x := Nat.le_add_left _ _
        constructor
        · by_cases hs : x ∈ seen
          · simp [hs, hx, hmem, wsum] at *; omega
          · simp [hs, hx, hmem, wsum] at *; omega
        · simp [wsum] at *; omega
      · rw [if_neg hx]
        constructor
        · by_cases hs : x ∈ seen
          · simp [List.filter_cons, hs, hx, hmem, wsum] at *; omega
          · simp [List.filter_cons, hs, hx, hmem, wsum] at *; omega
        · simp [wsum] at *; omega
  intro l
  obtain ⟨e, b⟩ := key l []
  have hz : (uniq l).filter (fun v => decide (v ∈ ([] : List Nat))) = [] := by
    rw [List.filter_congr (q := fun _ => false) (fun v _ => by simp)]
    exact Uniq.filt_false _
  rw [hz] at e
  simp only [wred, e, wsum, List.map_nil, List.sum_nil]
  simp only [wsum] at b
  omega

/-- Erasing one occurrence removes exactly its weight. -/
theorem wsum_erase (w : Nat → Nat) {x : Nat} : ∀ l : List Nat, x ∈ l →
    wsum w l = w x + wsum w (l.erase x) := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons y ys ih =>
    intro h
    by_cases hxy : y = x
    · subst hxy; simp [wsum, List.erase_cons_head]
    · have hx : x ∈ ys := (List.mem_cons.mp h).resolve_left (fun e => hxy e.symm)
      have := ih hx
      simp only [wsum] at this ⊢
      rw [List.erase_cons_tail (by simpa using hxy)]
      simp [this]; omega

/-- A duplicate-free list inside another weighs no more. -/
theorem cover (w : Nat → Nat) : ∀ (a b : List Nat), a.Nodup →
    (∀ x ∈ a, x ∈ b) → wsum w a ≤ wsum w b := by
  intro a
  induction a with
  | nil => intro _ _ _; simp [wsum]
  | cons x xs ih =>
    intro b hnd hsub
    have hx : x ∈ b := hsub x (by simp)
    have hxs : x ∉ xs := (List.nodup_cons.mp hnd).1
    have hsub' : ∀ y ∈ xs, y ∈ b.erase x := by
      intro y hy
      have hyx : y ≠ x := fun e => hxs (e ▸ hy)
      exact (List.mem_erase_of_ne hyx).mpr (hsub y (by simp [hy]))
    have := ih (b.erase x) (List.nodup_cons.mp hnd).2 hsub'
    rw [wsum_erase w b hx]
    simp only [wsum, List.map_cons, List.sum_cons] at this ⊢
    omega

/-- The witness set is a cheapest cover under every
    weighting at once: any list holding every color of the
    stream weighs at least as much as the witnesses. -/
theorem optimal (w : Nat → Nat) (l r : List Nat) (hr : ∀ x ∈ l, x ∈ r) :
    wsum w (uniq l) ≤ wsum w r :=
  cover w (uniq l) r (Uniq.nodup l) (fun x hx => hr x ((Uniq.mem l).mp hx))

/-- The redundant weight is the largest saving: keeping any
    cover of the stream's colors saves at most the redundant
    weight, under every weighting at once, and the witness set
    attains it. -/
theorem saving (w : Nat → Nat) (l r : List Nat) (hr : ∀ x ∈ l, x ∈ r) :
    wsum w l ≤ wred w l + wsum w r := by
  have h1 := split w l
  have h2 := optimal w l r hr
  omega

/-- Painting appended streams: nothing already painted is
    repainted. -/
theorem paint_append : ∀ (seen a b : List Nat),
    paint seen (a ++ b) = paint seen a ++ paint (a.reverse ++ seen) b := by
  intro seen a b
  induction a generalizing seen with
  | nil => simp [paint]
  | cons x xs ih =>
    simp only [List.cons_append, paint, List.reverse_cons, List.append_assoc]
    rw [ih]
    rfl

/-- The painting is a stream of the same colors. -/
theorem paint_colors : ∀ (seen l : List Nat), (paint seen l).map Prod.fst = l := by
  intro seen l
  induction l generalizing seen with
  | nil => rfl
  | cons x xs ih => simp [paint, ih]

/-- Unique witness: a color carries exactly one witness flag
    when it occurs and was not seen, and none otherwise. -/
theorem witness_unique (c : Nat) : ∀ (seen l : List Nat),
    ((paint seen l).filter (fun p => decide (p.1 = c) && p.2)).length
      = if c ∈ l ∧ c ∉ seen then 1 else 0 := by
  intro seen l
  induction l generalizing seen with
  | nil => simp [paint]
  | cons x xs ih =>
    have hih := ih (x :: seen)
    by_cases hxc : x = c
    · subst hxc
      by_cases hs : x ∈ seen <;> simp [paint, List.filter_cons, hs, hih]
    · simp [paint, List.filter_cons, hxc, hih]
      by_cases hc : c ∈ xs <;> by_cases hs : c ∈ seen <;> simp [hc, hs, Ne.symm hxc]

/-- Redundant marks weigh exactly the weighted measure: the
    weights read the painting, the painting never reads the
    weights. -/
theorem marks (w : Nat → Nat) : ∀ (seen l : List Nat),
    wa w seen l = (((paint seen l).filter (fun p => !p.2)).map (fun p => w p.1)).sum := by
  intro seen l
  induction l generalizing seen with
  | nil => rfl
  | cons x xs ih =>
    simp only [wa, paint, List.filter_cons, ih]
    by_cases hs : x ∈ seen <;> simp [hs]

/-- Witness flags count the distinct colors. -/
theorem witnesses (l : List Nat) :
    ((paint [] l).filter (fun p => p.2)).length = card l := by
  have h1 := marks (fun _ => 1) [] l
  have h2 := Exact.red_add_card l
  have h3 : (paint [] l).length = l.length := by
    have := congrArg List.length (paint_colors [] l)
    simpa using this
  rw [unit] at h1
  have h4 : ((paint [] l).filter (fun p => p.2)).length
      + ((paint [] l).filter (fun p => !p.2)).length = (paint [] l).length := by
    generalize paint [] l = q
    induction q with
    | nil => rfl
    | cons p ps ih =>
      cases hp : p.2 <;> simp [List.filter_cons, hp] <;> omega
  have h5 : (((paint [] l).filter (fun p => !p.2)).map (fun _ => 1)).sum
      = ((paint [] l).filter (fun p => !p.2)).length := by
    generalize (paint [] l).filter (fun p => !p.2) = q
    induction q with
    | nil => rfl
    | cons _ _ ih => simp [ih]; omega
  have hr : red l = aux [] l := rfl
  omega

/-- The incremental run state: what has been seen, and the
    weighted redundancy so far. -/
def run (w : Nat → Nat) : (List Nat × Nat) → List Nat → (List Nat × Nat)
  | st, [] => st
  | (seen, r), x :: xs => run w (x :: seen, r + (if x ∈ seen then w x else 0)) xs

/-- The run carries its seen list and adds the weighted
    counter. -/
theorem run_eq (w : Nat → Nat) : ∀ (l seen : List Nat) (r : Nat),
    run w (seen, r) l = (l.reverse ++ seen, r + wa w seen l) := by
  intro l
  induction l with
  | nil => intro seen r; simp [run, wa]
  | cons x xs ih =>
    intro seen r
    simp only [run, wa, ih, List.reverse_cons, List.append_assoc,
      List.singleton_append]
    congr 1
    omega

/-- Continuously additive: running over an appended stream is
    running over the new part from the old state, and it equals
    the from-scratch run. -/
theorem incremental (w : Nat → Nat) (a b : List Nat) :
    run w (run w ([], 0) a) b = run w ([], 0) (a ++ b)
      ∧ (run w ([], 0) (a ++ b)).2 = wred w (a ++ b) := by
  constructor
  · rw [run_eq, run_eq, run_eq, append]
    simp
  · rw [run_eq]; simp [wred]

end Color

/-- Colored configurations of a graph: its hyperedges painted
    by a structural key. -/
def colorRed (w : Nat → Nat) (key : (List Nat × Nat) → Nat) (g : Graph) : Nat :=
  wred w (g.edges.map key)

namespace Colored

/-- Colored redundancy is monotone under expansion, for every
    key and every weighting. -/
theorem grow (w : Nat → Nat) (key : (List Nat × Nat) → Nat) {g h : Graph}
    (hexp : Expands g h) : colorRed w key g ≤ colorRed w key h := by
  obtain ⟨dn, de, _, he⟩ := hexp
  simp only [colorRed, he, List.map_append]
  exact Color.left w _ _

/-- Colored redundancy is superadditive over joins, strictly
    by the weight of every shared color. -/
theorem sum_join (w : Nat → Nat) (key : (List Nat × Nat) → Nat) (g h : Graph) :
    colorRed w key g + colorRed w key h ≤ colorRed w key (Redundant.join g h) := by
  simp only [colorRed, Redundant.join, List.map_append]
  exact Color.sum w _ _

theorem strict_join (w : Nat → Nat) (key : (List Nat × Nat) → Nat) {g h : Graph}
    {e f : List Nat × Nat} (he : e ∈ g.edges) (hf : f ∈ h.edges) (hk : key e = key f) :
    colorRed w key g + colorRed w key h + w (key e) ≤ colorRed w key (Redundant.join g h) := by
  simp only [colorRed, Redundant.join, List.map_append]
  have hf' : key e ∈ h.edges.map key := by
    rw [hk]; exact List.mem_map_of_mem (f := key) hf
  exact Color.strict w (List.mem_map_of_mem (f := key) he) hf'

/-- Reordering hyperedges never changes colored redundancy. -/
theorem relist (w : Nat → Nat) (key : (List Nat × Nat) → Nat) {g h : Graph}
    (p : g.edges.Perm h.edges) : colorRed w key g = colorRed w key h :=
  Color.perm w (p.map key) []

/-- A structural key that ignores premise order makes colored
    redundancy invariant under premise re-listing too. -/
theorem premises (key : (List Nat × Nat) → Nat)
    (hkey : ∀ ps ps' c, ps.Perm ps' → key (ps, c) = key (ps', c))
    {es es' : List (List Nat × Nat)} (r : EdgeRelist es es') :
    es.map key = es'.map key := by
  induction r with
  | nil => rfl
  | cons hp _ ih => simp [ih, hkey _ _ _ hp]

end Colored

namespace Control

/-- Control weight: reweighting changes the value and not the
    painting. The same stream painted once, valued under two
    weightings. -/
theorem weight :
    paint [] [1, 1, 2] = [(1, true), (1, false), (2, true)]
      ∧ wred (fun _ => 1) [1, 1, 2] = 1
      ∧ wred (fun x => if x = 1 then 7 else 0) [1, 1, 2] = 7
      ∧ wred (fun _ => 0) [1, 1, 2] = 0 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- Control witness: an irredundant stream is all witnesses. -/
theorem allwit : paint [] [3, 1, 2] = [(3, true), (1, true), (2, true)] := by decide

end Control

#print axioms Color.unit
#print axioms Color.unit_red
#print axioms Color.append
#print axioms Color.mono
#print axioms Color.congr
#print axioms Color.add
#print axioms Color.scale
#print axioms Color.wmono
#print axioms Color.perm
#print axioms Color.pos
#print axioms Color.left
#print axioms Color.sum
#print axioms Color.strict
#print axioms Color.split
#print axioms Color.wsum_erase
#print axioms Color.cover
#print axioms Color.optimal
#print axioms Color.saving
#print axioms Color.paint_append
#print axioms Color.paint_colors
#print axioms Color.witness_unique
#print axioms Color.marks
#print axioms Color.witnesses
#print axioms Color.run_eq
#print axioms Color.incremental
#print axioms Colored.grow
#print axioms Colored.sum_join
#print axioms Colored.strict_join
#print axioms Colored.relist
#print axioms Colored.premises
#print axioms Control.weight
#print axioms Control.allwit

end Redundant
