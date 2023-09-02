theory Scratch
  imports Main
begin

definition rapp :: "'a ⇒ ('a ⇒ 'b) ⇒ 'b" (infixl "⇗" 60) where
  "a⇗b = b a"

definition lapp :: "('a ⇒ 'b) ⇒ 'a ⇒ 'b" (infixl "⇖" 60) where
  "b⇖a = b a"

datatype Object = pochi | dog | animal | apple | fruit

inductive is_a :: "Object ⇒ Object ⇒ bool" where
  "is_a pochi dog"
| "is_a dog animal"
| "is_a apple fruit"
| "is_a (adj x) x" 
| "is_a x x"
| "⟦is_a x y; is_a y z⟧ ⟹ is_a x z"

inductive run :: "Object ⇒ bool" where
  "⟦x⇗is_a⇖y; run x⟧ ⟹ run y"

inductive like :: "Object ⇒ Object ⇒ bool" where
  "⟦b⇗is_a⇖a; d⇗is_a⇖c; like a c⟧ ⟹ like b d"

fun do_not_1 :: "Object ⇒ (Object ⇒ bool) ⇒ bool " where
  "do_not_1 sb vb = (¬ (vb sb))"

fun do_not_2 :: "Object ⇒ (Object ⇒ Object ⇒ bool) ⇒ Object ⇒ bool" where
  "do_not_2 sb vb ob = (¬ (vb sb ob))"

text "A beautiful animal is an animal"
lemma "(beautiful animal)⇗is_a⇖animal"
  by (simp add: is_a.intros lapp_def rapp_def)

text "If pochi likes an animal then pochi like a dog"
lemma "pochi⇗like⇖animal ⟹ pochi⇗like⇖dog"
  using is_a.intros like.intros rapp_def lapp_def by metis

text "If pochi likes animal then some animals like an animal"
lemma "pochi⇗like⇖animal ⟹ ∃x. x⇗is_a⇖animal ∧ x ⇗like⇖animal"
  using is_a.intros like.intros rapp_def lapp_def by metis

text "If every dog likes a dog then dog likes an pochi"
lemma "∀x. x⇗is_a⇖dog ⟶ x⇗like⇖dog ⟹ dog⇗like⇖pochi"
  using is_a.intros like.intros lapp_def rapp_def by metis

text "If every dog likes pochi then dog likes pochi"
lemma "∀x. x⇗is_a⇖dog ⟶ x⇗like⇖pochi ⟹ dog⇗like⇖pochi"
  using is_a.intros like.intros lapp_def rapp_def by metis

text "If a dog likes any fruit then pochi likes an apple"
lemma "∀x. x⇗is_a⇖fruit ⟶ dog⇗like⇖x ⟹ pochi⇗like⇖apple"
  using is_a.intros like.intros lapp_def rapp_def by metis

text "If every animal runs then a dog runs"
lemma "∀x. x⇗is_a⇖animal ⟶ x⇗run ⟹ dog⇗run"
  using is_a.intros like.intros lapp_def rapp_def by metis

text "If a dog runs then an animal runs"
lemma "dog⇗run ⟹ animal⇗run"
  using is_a.intros run.intros lapp_def rapp_def by metis

text "If no animal run then dog does not run"
lemma "∀x. x⇗is_a⇖animal ⟶ x⇗do_not_1⇖run ⟹ dog⇗do_not_1⇖run"
  by (simp add: is_a.intros lapp_def rapp_def)

text "If no animal likes an apple then a dog does not like apple"
lemma "∀x. x⇗is_a⇖animal ⟶ x⇗do_not_2⇖like⇖apple ⟹ dog⇗do_not_2⇖like⇖apple"
  by (simp add: is_a.intros lapp_def rapp_def)
  
end
