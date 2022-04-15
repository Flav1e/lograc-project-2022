-- BigStep



module BigStep where



open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; sym; cong-app)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Untyped
  using (Context; _⊢_; _∋_; ★; ∅; _,_; Z; S_; `_; #_; ƛ_; _·_;
  subst; subst-zero; exts; rename; β; ξ₁; ξ₂; ζ; _—→_; _—↠_; _—→⟨_⟩_; _∎;
  —↠-trans; appL-cong)
open import Substitution using (Subst; ids)



ClosEnv : Context → Set

data Clos : Set where
  clos : ∀{Γ} → (M : Γ ⊢ ★) → ClosEnv Γ → Clos

ClosEnv Γ = ∀ (x : Γ ∋ ★) → Clos



∅' : ClosEnv ∅
∅' ()

_,'_ : ∀ {Γ} → ClosEnv Γ → Clos → ClosEnv (Γ , ★)
(γ ,' c) Z = c
(γ ,' c) (S x) = γ x



data _⊢_⇓_ : ∀{Γ} → ClosEnv Γ → (Γ ⊢ ★) → Clos → Set where

  ⇓-var : ∀{Γ}{γ : ClosEnv Γ}{x : Γ ∋ ★}{Δ}{δ : ClosEnv Δ}{M : Δ ⊢ ★}{V}
    → γ x ≡ clos M δ
    → δ ⊢ M ⇓ V
      -----------
    → γ ⊢ ` x ⇓ V

  ⇓-lam : ∀{Γ}{γ : ClosEnv Γ}{M : Γ , ★ ⊢ ★}
    → γ ⊢ ƛ M ⇓ clos (ƛ M) γ

  ⇓-app : ∀{Γ}{γ : ClosEnv Γ}{L M : Γ ⊢ ★}{Δ}{δ : ClosEnv Δ}{N : Δ , ★ ⊢ ★}{V}
    → γ ⊢ L ⇓ clos (ƛ N) δ   →   (δ ,' clos M γ) ⊢ N ⇓ V
      ---------------------------------------------------
    → γ ⊢ L · M ⇓ V




-- Your code goes here


⇓-determ : ∀{Γ}{γ : ClosEnv Γ}{M : Γ ⊢ ★}{V V' : Clos}
  → γ ⊢ M ⇓ V → γ ⊢ M ⇓ V'
  → V ≡ V'
⇓-determ (⇓-var eq1 mc) (⇓-var eq2 mc')
    with trans (sym eq1) eq2
... | refl = ⇓-determ mc mc'
⇓-determ ⇓-lam ⇓-lam = refl
⇓-determ (⇓-app mc mc₁) (⇓-app mc' mc'')
    with ⇓-determ mc mc'
... | refl = ⇓-determ mc₁ mc''





_≈_ : Clos → (∅ ⊢ ★) → Set
_≈ₑ_ : ∀{Γ} → ClosEnv Γ → Subst Γ ∅ → Set

(clos {Γ} M γ) ≈ N = Σ[ σ ∈ Subst Γ ∅ ] γ ≈ₑ σ × (N ≡ subst σ M)

γ ≈ₑ σ = ∀{x} → (γ x) ≈ (σ x)






≈ₑ-id : ∅' ≈ₑ ids
≈ₑ-id {()}



sub-id : ∀{Γ} {A} {M : Γ ⊢ A} → subst ids M ≡ M
sub-id = plfa.part2.Substitution.sub-id



ext-subst : ∀{Γ Δ} → Subst Γ Δ → Δ ⊢ ★ → Subst (Γ , ★) Δ
ext-subst{Γ}{Δ} σ N {A} = subst (subst-zero N) ∘ exts σ






subst-zero-exts : ∀{Γ Δ}{σ : Subst Γ Δ}{B}{M : Δ ⊢ B}{x : Γ ∋ ★}
  → (subst (subst-zero M) ∘ exts σ) (S x) ≡ σ x
subst-zero-exts {Γ}{Δ}{σ}{B}{M}{x} =
   cong-app (plfa.part2.Substitution.subst-zero-exts-cons{σ = σ}) (S x)





≈ₑ-ext : ∀ {Γ} {γ : ClosEnv Γ} {σ : Subst Γ ∅} {V} {N : ∅ ⊢ ★}
  → γ ≈ₑ σ  →  V ≈ N
    --------------------------
  → (γ ,' V) ≈ₑ (ext-subst σ N)
≈ₑ-ext {Γ} {γ} {σ} {V} {N} γ≈ₑσ V≈N {Z} = V≈N
≈ₑ-ext {Γ} {γ} {σ} {V} {N} γ≈ₑσ V≈N {S x}
  rewrite subst-zero-exts {σ = σ}{M = N}{x} = γ≈ₑσ




sub-sub : ∀{Γ Δ Σ}{A}{M : Γ ⊢ A} {σ₁ : Subst Γ Δ}{σ₂ : Subst Δ Σ}
  → subst σ₂ (subst σ₁ M) ≡ subst (subst σ₂ ∘ σ₁) M
sub-sub {M = M} = plfa.part2.Substitution.sub-sub {M = M}




⇓→—↠×≈ : ∀{Γ}{γ : ClosEnv Γ}{σ : Subst Γ ∅}{M : Γ ⊢ ★}{V : Clos}
       → γ ⊢ M ⇓ V  →  γ ≈ₑ σ
         ---------------------------------------
       → Σ[ N ∈ ∅ ⊢ ★ ] (subst σ M —↠ N) × V ≈ N
⇓→—↠×≈ {γ = γ} (⇓-var{x = x} γx≡Lδ δ⊢L⇓V) γ≈ₑσ
    with γ x | γ≈ₑσ {x} | γx≡Lδ
... | clos L δ | ⟨ τ , ⟨ δ≈ₑτ , σx≡τL ⟩ ⟩ | refl
      with ⇓→—↠×≈{σ = τ} δ⊢L⇓V δ≈ₑτ
...   | ⟨ N , ⟨ τL—↠N , V≈N ⟩ ⟩ rewrite σx≡τL =
        ⟨ N , ⟨ τL—↠N , V≈N ⟩ ⟩
⇓→—↠×≈ {σ = σ} {V = clos (ƛ N) γ} (⇓-lam) γ≈ₑσ =
    ⟨ subst σ (ƛ N) , ⟨ subst σ (ƛ N) ∎ , ⟨ σ , ⟨ γ≈ₑσ , refl ⟩ ⟩ ⟩ ⟩
⇓→—↠×≈{Γ}{γ} {σ = σ} {L · M} {V} (⇓-app {N = N} L⇓ƛNδ N⇓V) γ≈ₑσ
    with ⇓→—↠×≈{σ = σ} L⇓ƛNδ γ≈ₑσ
... | ⟨ _ , ⟨ σL—↠ƛτN , ⟨ τ , ⟨ δ≈ₑτ , ≡ƛτN ⟩ ⟩ ⟩ ⟩ rewrite ≡ƛτN
      with ⇓→—↠×≈ {σ = ext-subst τ (subst σ M)} N⇓V
             (λ {x} → ≈ₑ-ext{σ = τ} δ≈ₑτ ⟨ σ , ⟨ γ≈ₑσ , refl ⟩ ⟩ {x})
           | β{∅}{subst (exts τ) N}{subst σ M}
...   | ⟨ N' , ⟨ —↠N' , V≈N' ⟩ ⟩ | ƛτN·σM—→
        rewrite sub-sub{M = N}{σ₁ = exts τ}{σ₂ = subst-zero (subst σ M)} =
        let rs = (ƛ subst (exts τ) N) · subst σ M —→⟨ ƛτN·σM—→ ⟩ —↠N' in
        let g = —↠-trans (appL-cong σL—↠ƛτN) rs in
        ⟨ N' , ⟨ g , V≈N' ⟩ ⟩



cbn→reduce :  ∀{M : ∅ ⊢ ★}{Δ}{δ : ClosEnv Δ}{N′ : Δ , ★ ⊢ ★}
  → ∅' ⊢ M ⇓ clos (ƛ N′) δ
    -----------------------------
  → Σ[ N ∈ ∅ , ★ ⊢ ★ ] (M —↠ ƛ N)
cbn→reduce {M}{Δ}{δ}{N′} M⇓c
    with ⇓→—↠×≈{σ = ids} M⇓c ≈ₑ-id
... | ⟨ N , ⟨ rs , ⟨ σ , ⟨ h , eq2 ⟩ ⟩ ⟩ ⟩ rewrite sub-id{M = M} | eq2 =
      ⟨ subst (exts σ) N′ , rs ⟩




-- Your code goes here


{-
## Unicode

This chapter uses the following unicode:

    ≈  U+2248  ALMOST EQUAL TO (\~~ or \approx)
    ₑ  U+2091  LATIN SUBSCRIPT SMALL LETTER E (\_e)
    ⊢  U+22A2  RIGHT TACK (\|- or \vdash)
    ⇓  U+21DB  DOWNWARDS DOUBLE ARROW (\d= or \Downarrow)
-}