import topology.basic

open set

theorem open_set_for_each 
  (X : Type*)
  [topological_space X]
  (A : set X) 
  (h₀ : ∀ x ∈ A, ∃ (U : set X), is_open U ∧ x ∈ U ∧ U ⊆ A) : 
  is_open A :=
begin
  choose! f hf using h₀,
  have : A = ⋃ x ∈ A, f x,
  {
    ext p,
    split, 
    {
      intro hp,
      have hfp := hf p hp,
      rw mem_Union,
      use p,
      rw mem_Union,
      use hp,
      exact hfp.2.1,
    },
    {
      intro hp,
      rw mem_Union at hp,
      cases hp with i hi,
      rw mem_Union at hi,
      cases hi with hia hpfi,
      have x := hf i hia,
      exact x.2.2 hpfi,
    }
  },
  rw this,
  apply is_open_bUnion,
  intros i hi,
  exact (hf i hi).1,
end 
