-- Confluence



module Confluence where




open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (_∘_)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Substitution using (Rename; Subst)
open import Untyped
  using (_—→_; β; ξ₁; ξ₂; ζ; _—↠_; begin_; _—→⟨_⟩_; _—↠⟨_⟩_; _∎;
  abs-cong; appL-cong; appR-cong; —↠-trans;
  _⊢_; _∋_; `_; #_; _,_; ★; ƛ_; _·_; _[_];
  rename; ext; exts; Z; S_; subst; subst-zero)




infix 2 _⇛_

data _⇛_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  pvar : ∀{Γ A}{x : Γ ∋ A}
      ---------
    → (` x) ⇛ (` x)

  pabs : ∀{Γ}{N N′ : Γ , ★ ⊢ ★}
    → N ⇛ N′
      ----------
    → ƛ N ⇛ ƛ N′

  papp : ∀{Γ}{L L′ M M′ : Γ ⊢ ★}
    → L ⇛ L′
    → M ⇛ M′
      -----------------
    → L · M ⇛ L′ · M′

  pbeta : ∀{Γ}{N N′  : Γ , ★ ⊢ ★}{M M′ : Γ ⊢ ★}
    → N ⇛ N′
    → M ⇛ M′
      -----------------------
    → (ƛ N) · M  ⇛  N′ [ M′ ]




par-refl : ∀{Γ A}{M : Γ ⊢ A} → M ⇛ M
par-refl {Γ} {A} {` x} = pvar
par-refl {Γ} {★} {ƛ N} = pabs par-refl
par-refl {Γ} {★} {L · M} = papp par-refl par-refl



infix  2 _⇛*_
infixr 2 _⇛⟨_⟩_
infix  3 _∎

data _⇛*_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

  _∎ : ∀ {Γ A} (M : Γ ⊢ A)
      --------
    → M ⇛* M

  _⇛⟨_⟩_ : ∀ {Γ A} (L : Γ ⊢ A) {M N : Γ ⊢ A}
    → L ⇛ M
    → M ⇛* N
      ---------
    → L ⇛* N






-- Your code goes here





beta-par : ∀{Γ A}{M N : Γ ⊢ A}
  → M —→ N
    ------
  → M ⇛ N
beta-par {Γ} {★} {L · M} (ξ₁ r) = papp (beta-par {M = L} r) par-refl
beta-par {Γ} {★} {L · M} (ξ₂ r) = papp par-refl (beta-par {M = M} r)
beta-par {Γ} {★} {(ƛ N) · M} β = pbeta par-refl par-refl
beta-par {Γ} {★} {ƛ N} (ζ r) = pabs (beta-par r)




betas-pars : ∀{Γ A} {M N : Γ ⊢ A}
  → M —↠ N
    ------
  → M ⇛* N
betas-pars {Γ} {A} {M₁} {.M₁} (M₁ ∎) = M₁ ∎
betas-pars {Γ} {A} {.L} {N} (L —→⟨ b ⟩ bs) =
   L ⇛⟨ beta-par b ⟩ betas-pars bs





par-betas : ∀{Γ A}{M N : Γ ⊢ A}
  → M ⇛ N
    ------
  → M —↠ N
par-betas {Γ} {A} {.(` _)} (pvar{x = x}) = (` x) ∎
par-betas {Γ} {★} {ƛ N} (pabs p) = abs-cong (par-betas p)
par-betas {Γ} {★} {L · M} (papp {L = L}{L′}{M}{M′} p₁ p₂) =
    begin
    L · M   —↠⟨ appL-cong{M = M} (par-betas p₁) ⟩
    L′ · M  —↠⟨ appR-cong (par-betas p₂) ⟩
    L′ · M′
    ∎
par-betas {Γ} {★} {(ƛ N) · M} (pbeta{N′ = N′}{M′ = M′} p₁ p₂) =
    begin
    (ƛ N) · M                    —↠⟨ appL-cong{M = M} (abs-cong (par-betas p₁)) ⟩
    (ƛ N′) · M                   —↠⟨ appR-cong{L = ƛ N′} (par-betas p₂)  ⟩
    (ƛ N′) · M′                  —→⟨ β ⟩
     N′ [ M′ ]
    ∎





pars-betas : ∀{Γ A} {M N : Γ ⊢ A}
  → M ⇛* N
    ------
  → M —↠ N
pars-betas (M₁ ∎) = M₁ ∎
pars-betas (L ⇛⟨ p ⟩ ps) = —↠-trans (par-betas p) (pars-betas ps)






par-subst : ∀{Γ Δ} → Subst Γ Δ → Subst Γ Δ → Set
par-subst {Γ}{Δ} σ σ′ = ∀{A}{x : Γ ∋ A} → σ x ⇛ σ′ x





rename-subst-commute : ∀{Γ Δ}{N : Γ , ★ ⊢ ★}{M : Γ ⊢ ★}{ρ : Rename Γ Δ }
    → (rename (ext ρ) N) [ rename ρ M ] ≡ rename ρ (N [ M ])
rename-subst-commute {N = N} = plfa.part2.Substitution.rename-subst-commute {N = N}





par-rename : ∀{Γ Δ A} {ρ : Rename Γ Δ} {M M′ : Γ ⊢ A}
  → M ⇛ M′
    ------------------------
  → rename ρ M ⇛ rename ρ M′
par-rename pvar = pvar
par-rename (pabs p) = pabs (par-rename p)
par-rename (papp p₁ p₂) = papp (par-rename p₁) (par-rename p₂)
par-rename {Γ}{Δ}{A}{ρ} (pbeta{Γ}{N}{N′}{M}{M′} p₁ p₂)
    with pbeta (par-rename{ρ = ext ρ} p₁) (par-rename{ρ = ρ} p₂)
... | G rewrite rename-subst-commute{Γ}{Δ}{N′}{M′}{ρ} = G






par-subst-exts : ∀{Γ Δ} {σ τ : Subst Γ Δ}
  → par-subst σ τ
    ------------------------------------------
  → ∀{B} → par-subst (exts σ {B = B}) (exts τ)
par-subst-exts s {x = Z} = pvar
par-subst-exts s {x = S x} = par-rename s





subst-commute : ∀{Γ Δ}{N : Γ , ★ ⊢ ★}{M : Γ ⊢ ★}{σ : Subst Γ Δ }
  → subst (exts σ) N [ subst σ M ] ≡ subst σ (N [ M ])
subst-commute {N = N} = plfa.part2.Substitution.subst-commute {N = N}





subst-par : ∀{Γ Δ A} {σ τ : Subst Γ Δ} {M M′ : Γ ⊢ A}
  → par-subst σ τ  →  M ⇛ M′
    --------------------------
  → subst σ M ⇛ subst τ M′
subst-par {Γ} {Δ} {A} {σ} {τ} {` x} s pvar = s
subst-par {Γ} {Δ} {A} {σ} {τ} {ƛ N} s (pabs p) =
  pabs (subst-par {σ = exts σ} {τ = exts τ}
        (λ {A}{x} → par-subst-exts s {x = x}) p)
subst-par {Γ} {Δ} {★} {σ} {τ} {L · M} s (papp p₁ p₂) =
  papp (subst-par s p₁) (subst-par s p₂)
subst-par {Γ} {Δ} {★} {σ} {τ} {(ƛ N) · M} s (pbeta{N′ = N′}{M′ = M′} p₁ p₂)
    with pbeta (subst-par{σ = exts σ}{τ = exts τ}{M = N}
                        (λ{A}{x} → par-subst-exts s {x = x}) p₁)
               (subst-par {σ = σ} s p₂)
... | G rewrite subst-commute{N = N′}{M = M′}{σ = τ} = G




par-subst-zero : ∀{Γ}{A}{M M′ : Γ ⊢ A}
       → M ⇛ M′
       → par-subst (subst-zero M) (subst-zero M′)
par-subst-zero {M} {M′} p {A} {Z} = p
par-subst-zero {M} {M′} p {A} {S x} = pvar





sub-par : ∀{Γ A B} {N N′ : Γ , A ⊢ B} {M M′ : Γ ⊢ A}
  → N ⇛ N′
  → M ⇛ M′
    --------------------------
  → N [ M ] ⇛ N′ [ M′ ]
sub-par pn pm = subst-par (par-subst-zero pm) pn





_⁺ : ∀ {Γ A}
  → Γ ⊢ A → Γ ⊢ A
(` x) ⁺       =  ` x
(ƛ M) ⁺       = ƛ (M ⁺)
((ƛ N) · M) ⁺ = N ⁺ [ M ⁺ ]
(L · M) ⁺     = L ⁺ · (M ⁺)

par-triangle : ∀ {Γ A} {M N : Γ ⊢ A}
  → M ⇛ N
    -------
  → N ⇛ M ⁺
par-triangle pvar          = pvar
par-triangle (pabs p)      = pabs (par-triangle p)
par-triangle (pbeta p1 p2) = sub-par (par-triangle p1) (par-triangle p2)
par-triangle (papp {L = ƛ _ } (pabs p1) p2) =
  pbeta (par-triangle p1) (par-triangle p2)
par-triangle (papp {L = ` _}   p1 p2) = papp (par-triangle p1) (par-triangle p2)
par-triangle (papp {L = _ · _} p1 p2) = papp (par-triangle p1) (par-triangle p2)




par-diamond : ∀{Γ A} {M N N′ : Γ ⊢ A}
  → M ⇛ N
  → M ⇛ N′
    ---------------------------------
  → Σ[ L ∈ Γ ⊢ A ] (N ⇛ L) × (N′ ⇛ L)
par-diamond {M = M} p1 p2 = ⟨ M ⁺ , ⟨ par-triangle p1 , par-triangle p2 ⟩ ⟩





strip : ∀{Γ A} {M N N′ : Γ ⊢ A}
  → M ⇛ N
  → M ⇛* N′
    ------------------------------------
  → Σ[ L ∈ Γ ⊢ A ] (N ⇛* L)  ×  (N′ ⇛ L)
strip{Γ}{A}{M}{N}{N′} mn (M ∎) = ⟨ N , ⟨ N ∎ , mn ⟩ ⟩
strip{Γ}{A}{M}{N}{N′} mn (M ⇛⟨ mm' ⟩ m'n')
  with strip (par-triangle mm') m'n'
... | ⟨ L , ⟨ ll' , n'l' ⟩ ⟩ = ⟨ L , ⟨ N ⇛⟨ par-triangle mn ⟩ ll' , n'l' ⟩ ⟩





par-confluence : ∀{Γ A} {L M₁ M₂ : Γ ⊢ A}
  → L ⇛* M₁
  → L ⇛* M₂
    ------------------------------------
  → Σ[ N ∈ Γ ⊢ A ] (M₁ ⇛* N) × (M₂ ⇛* N)
par-confluence {Γ}{A}{L}{.L}{N} (L ∎) L⇛*N = ⟨ N , ⟨ L⇛*N , N ∎ ⟩ ⟩
par-confluence {Γ}{A}{L}{M₁′}{M₂} (L ⇛⟨ L⇛M₁ ⟩ M₁⇛*M₁′) L⇛*M₂
    with strip L⇛M₁ L⇛*M₂
... | ⟨ N , ⟨ M₁⇛*N , M₂⇛N ⟩ ⟩
      with par-confluence M₁⇛*M₁′ M₁⇛*N
...   | ⟨ N′ , ⟨ M₁′⇛*N′ , N⇛*N′ ⟩ ⟩ =
        ⟨ N′ , ⟨ M₁′⇛*N′ , (M₂ ⇛⟨ M₂⇛N ⟩ N⇛*N′) ⟩ ⟩





confluence : ∀{Γ A} {L M₁ M₂ : Γ ⊢ A}
  → L —↠ M₁
  → L —↠ M₂
    -----------------------------------
  → Σ[ N ∈ Γ ⊢ A ] (M₁ —↠ N) × (M₂ —↠ N)
confluence L↠M₁ L↠M₂
    with par-confluence (betas-pars L↠M₁) (betas-pars L↠M₂)
... | ⟨ N , ⟨ M₁⇛N , M₂⇛N ⟩ ⟩ =
      ⟨ N , ⟨ pars-betas M₁⇛N , pars-betas M₂⇛N ⟩ ⟩




{- 
## Unicode

This chapter uses the following unicode:

    ⇛  U+21DB  RIGHTWARDS TRIPLE ARROW (\r== or \Rrightarrow)
    ⁺  U+207A  SUPERSCRIPT PLUS SIGN   (\^+)
-}