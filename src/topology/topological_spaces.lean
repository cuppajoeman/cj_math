import topology.basic
import data.real.nnreal
import data.real.basic

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
      rw mem_Union₂,
      use p,
      exact ⟨ hp, hfp.2.1 ⟩,
    },
    {
      intro hp,
      rw mem_Union₂ at hp,
      cases hp with i hi,
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



def intersection_of_topologies {X : Type*} {ι : Sort*}
  (f : ι → topological_space X) : topological_space X :=
{ is_open := λ s, ∀ i, (f i).is_open s,
  is_open_univ := 
  begin
    sorry
  end,
  is_open_inter := 
  begin
    intros s t hos hot i,
    specialize hos i,
    specialize hot i,
    exact (f i).is_open_inter s t hos hot,
  end,
  is_open_sUnion := sorry }