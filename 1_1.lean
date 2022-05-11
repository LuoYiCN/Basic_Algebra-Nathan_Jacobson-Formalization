import algebra.group.defs
import data.subtype
import data.set.basic
import data.vector.basic
import tactic

/-
# following definitions can be found in algebra/group/defs
# definition of semigroup:
class semigroup (G : Type u) extends has_mul G :=
(mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
# definition of mul_one_class:
class mul_one_class (M : Type u) extends has_one M, has_mul M :=
(one_mul : ∀ (a : M), 1 * a = a)
(mul_one : ∀ (a : M), a * 1 = a)
# definition of monoid:
class monoid (M : Type u) extends semigroup M, mul_one_class M :=
(npow : ℕ → M → M := npow_rec)
(npow_zero' : ∀ x, npow 0 x = 1 . try_refl_tac)
(npow_succ' : ∀ (n : ℕ) x, npow n.succ x = x * npow n x . try_refl_tac)
# following definition can be found in group_theory/submonoid/basics
# definiton of submonoid:
structure submonoid (M : Type*) [mul_one_class M] :=
(carrier : set M)
(one_mem' : (1 : M) ∈ carrier)
(mul_mem' {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier)
-/

instance exercise_1_1_1 (T:Type*) (S:set T) : semigroup S :={
  mul:=λ a b, b,
  mul_assoc := by{simp_intros,}
}

namespace e1_2
@[simp]
def mul:(ℤ×ℤ)→(ℤ×ℤ)→(ℤ×ℤ):=λ x y,(x.1*y.1+2*x.2*y.2,x.1*y.2+x.2*y.1)
instance excersice_1_1_2 : mul_one_class (ℤ×ℤ):={
  one:=(1,0),
  mul:=mul,
  one_mul:=by{simp,},
  mul_one:=by{simp,},
}
end e1_2
section
open vector
variable T : Type* 
def mul : vector T 8 → vector T 8 → vector T 8 := 
λ a b, append (take 5 a) (drop 5 b)

instance word_mul : has_mul (vector T 8) :=⟨mul T⟩

instance exercise_1_1_3 : semigroup (vector T 8) := by{
  fconstructor,
    exact (word_mul T).mul,
  intros,
  cases a,cases b,cases c,
  dsimp [(*),mul,vector.take,vector.drop,vector.append],
  simp [list.take_append,list.take_append_eq_append_take,a_property,
  list.take_take,list.drop_append_eq_append_drop,b_property],
  
}
end
instance execercise_1_1_4 (M G:Type*) [semigroup M] (pm : M) : semigroup M:=by{
  fconstructor,
  exact (λ a b,a*pm*b),
  simp [mul_assoc],
}

section
open classical
local attribute [instance] prop_decidable
lemma e1_1_5 (T:Type*) (S M: set T) (u:T) (M=S∪{u})(a:↥M)(H:↑a≠u) (u∉S)
 : ↑a∈S:=by{
  unfold_coes at *,
  cases a,
  dsimp at *,
  rw [H] at a_property,
  replace H_1 := set.mem_or_mem_of_mem_union a_property,
  cases H_1,assumption,
  solve_by_elim, 
}
instance execercise_1_1_5 (T:Type*) (S M: set T) [semigroup S] (u:T) (H1:u∉S)
(M=S∪{u}):monoid M:=by{
  fconstructor,{
    intros a b,
    by_cases h0:↑a=u,
      exact b,
    by_cases ↑b=u,
      exact a,
    have h0:=e1_1_5 T S S u M H a h0 u H1,
    have h1:=e1_1_5 T S S u M H b h u H1,
    casesI _inst_1,
    let c:= mul ⟨a,h0⟩ ⟨b,h1⟩,
    exact ⟨c,(by{
      have h2:↑c∈S,simp,
      rw H,
      refine ({u}:set T).mem_union_left h2,
    }:↑c∈M)⟩,
  },{
    casesI _inst_1,
    intros a b c,
    by_cases h0:↑a=u,{
      conv_lhs{
        congr,
        simp,       
        rw [dif_pos h0],
      },
      conv_rhs{
        simp,
        rw [dif_pos h0],
      },
    },
    by_cases h1:↑b=u,{
      conv_lhs{
        congr,
        simp,       
        rw [dif_neg h0,dif_pos h1],
      },
      conv_rhs{
        congr,
        skip,
        simp,
        rw [dif_pos h1],
      },
    },
    by_cases h2:↑c=u,{
      simp [dif_pos h2,dif_neg h0,dif_neg h1],
      intro h3,
      ext,
      unfold_coes at *,
      finish,
    },
    have  h4:=e1_1_5 T S S u M H a h0 u H1,
    have  h5:=e1_1_5 T S S u M H b h1 u H1,
    have  h6:=e1_1_5 T S S u M H c h2 u H1,
    have  h3:=mul_assoc ⟨↑a,h4⟩ ⟨↑b,h5⟩ ⟨↑c,h6⟩,
    have h7:↑(mul ⟨↑a,h4⟩ ⟨↑b,h5⟩) ≠ u,by{
      generalize : (mul ⟨↑a, h4⟩ ⟨↑b, h5⟩) = x,
      have h7:↑x∈S,simp,
      by_contra,
      rw h at h7,
      finish,
    },
    have h8:↑(mul ⟨↑b,h5⟩ ⟨↑c,h6⟩) ≠ u,{
      generalize : (mul ⟨↑b,h5⟩ ⟨↑c,h6⟩) = x,
      have h7:↑x∈S,simp,
      by_contra,
      rw h at h7,
      finish,
    },
    simp [dif_neg h0,dif_neg h1,dif_neg h2,dif_neg h7,dif_neg h8] at h3 |-,
    refine congr_arg coe h3,
  },{
    exact ⟨u,(by{
      have h0:u∈{u},refine set.mem_singleton u,
      rw H,
      refine set.mem_union_right S h0,
    }:u∈M)⟩,
  },{
    intro a,
    simp,
  },{
    intro a,
    simp,
    intro h,
    unfold_coes at *,
    cases a,
    dsimp at *,
    ext,
    unfold_coes,
    dsimp,
    exact h.symm,
  },
  /-what left is the definition of pow and two properties about it, not part
  of standard definition of a monoid, omitted-/
  repeat {sorry},
}
end

