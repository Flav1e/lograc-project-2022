--Substitution

module Substitution where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Function using (_∘_)
open import Untyped
     using (Type; Context; _⊢_; ★; _∋_; ∅; _,_; Z; S_; `_; ƛ_; _·_;
            rename; subst; ext; exts; _[_]; subst-zero)

postulate
  extensionality : ∀ {A B : Set} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g

Rename : Context → Context → Set
Rename Γ Δ = ∀{A} → Γ ∋ A → Δ ∋ A

Subst : Context → Context → Set
Subst Γ Δ = ∀{A} → Γ ∋ A → Δ ⊢ A

⟪_⟫ : ∀{Γ Δ A} → Subst Γ Δ → Γ ⊢ A → Δ ⊢ A
⟪ σ ⟫ = λ M → subst σ M

ids : ∀{Γ} → Subst Γ Γ
ids x = ` x

↑ : ∀{Γ A} → Subst Γ (Γ , A)
↑ x = ` (S x)

infixr 6 _•_

_•_ : ∀{Γ Δ A} → (Δ ⊢ A) → Subst Γ Δ → Subst (Γ , A) Δ
(M • σ) Z = M
(M • σ) (S x) = σ x

infixr 5 _⨟_

_⨟_ : ∀{Γ Δ Σ} → Subst Γ Δ → Subst Δ Σ → Subst Γ Σ
σ ⨟ τ = ⟪ τ ⟫ ∘ σ

ren : ∀{Γ Δ} → Rename Γ Δ → Subst Γ Δ
ren ρ = ids ∘ ρ

sub-head : ∀ {Γ Δ} {A} {M : Δ ⊢ A}{σ : Subst Γ Δ}
         → ⟪ M • σ ⟫ (` Z) ≡ M
sub-head = refl

sub-tail : ∀{Γ Δ} {A B} {M : Δ ⊢ A} {σ : Subst Γ Δ}
         → (↑ ⨟ M • σ) {A = B} ≡ σ
sub-tail = extensionality λ x → refl

sub-η : ∀{Γ Δ} {A B} {σ : Subst (Γ , A) Δ}
      → (⟪ σ ⟫ (` Z) • (↑ ⨟ σ)) {A = B} ≡ σ
sub-η {Γ}{Δ}{A}{B}{σ} = extensionality λ x → lemma
   where
   lemma : ∀ {x} → ((⟪ σ ⟫ (` Z)) • (↑ ⨟ σ)) x ≡ σ x
   lemma {x = Z} = refl
   lemma {x = S x} = refl

Z-shift : ∀{Γ}{A B}
        → ((` Z) • ↑) ≡ ids {Γ , A} {B}
Z-shift {Γ}{A}{B} = extensionality lemma
   where
   lemma : (x : Γ , A ∋ B) → ((` Z) • ↑) x ≡ ids x
   lemma Z = refl
   lemma (S y) = refl

sub-idL : ∀{Γ Δ} {σ : Subst Γ Δ} {A}
       → ids ⨟ σ ≡ σ {A}
sub-idL = extensionality λ x → refl

sub-dist :  ∀{Γ Δ Σ : Context} {A B} {σ : Subst Γ Δ} {τ : Subst Δ Σ}
              {M : Δ ⊢ A}
         → ((M • σ) ⨟ τ) ≡ ((subst τ M) • (σ ⨟ τ)) {B}
sub-dist {Γ}{Δ}{Σ}{A}{B}{σ}{τ}{M} = extensionality λ x → lemma {x = x}
  where
  lemma : ∀ {x : Γ , A ∋ B} → ((M • σ) ⨟ τ) x ≡ ((subst τ M) • (σ ⨟ τ)) x
  lemma {x = Z} = refl
  lemma {x = S x} = refl

sub-app : ∀{Γ Δ} {σ : Subst Γ Δ} {L : Γ ⊢ ★}{M : Γ ⊢ ★}
        → ⟪ σ ⟫ (L · M)  ≡ (⟪ σ ⟫ L) · (⟪ σ ⟫ M)
sub-app = refl

cong-ext : ∀{Γ Δ}{ρ ρ′ : Rename Γ Δ}{B}
   → (∀{A} → ρ ≡ ρ′ {A})
     ---------------------------------
   → ∀{A} → ext ρ {B = B} ≡ ext ρ′ {A}
cong-ext{Γ}{Δ}{ρ}{ρ′}{B} rr {A} = extensionality λ x → lemma {x}
  where
  lemma : ∀{x : Γ , B ∋ A} → ext ρ x ≡ ext ρ′ x
  lemma {Z} = refl
  lemma {S y} = cong S_ (cong-app rr y)

cong-rename : ∀{Γ Δ}{ρ ρ′ : Rename Γ Δ}{B}{M : Γ ⊢ B}
        → (∀{A} → ρ ≡ ρ′ {A})
          ------------------------
        → rename ρ M ≡ rename ρ′ M
cong-rename {M = ` x} rr = cong `_ (cong-app rr x)
cong-rename {ρ = ρ} {ρ′ = ρ′} {M = ƛ N} rr =
   cong ƛ_ (cong-rename {ρ = ext ρ}{ρ′ = ext ρ′}{M = N} (cong-ext rr))
cong-rename {M = L · M} rr =
   cong₂ _·_ (cong-rename rr) (cong-rename rr)

cong-exts : ∀{Γ Δ}{σ σ′ : Subst Γ Δ}{B}
   → (∀{A} → σ ≡ σ′ {A})
     -----------------------------------
   → ∀{A} → exts σ {B = B} ≡ exts σ′ {A}
cong-exts{Γ}{Δ}{σ}{σ′}{B} ss {A} = extensionality λ x → lemma {x}
   where
   lemma : ∀{x} → exts σ x ≡ exts σ′ x
   lemma {Z} = refl
   lemma {S x} = cong (rename S_) (cong-app (ss {A}) x)

cong-sub : ∀{Γ Δ}{σ σ′ : Subst Γ Δ}{A}{M M′ : Γ ⊢ A}
            → (∀{A} → σ ≡ σ′ {A})  →  M ≡ M′
              ------------------------------
            → subst σ M ≡ subst σ′ M′
cong-sub {Γ} {Δ} {σ} {σ′} {A} {` x} ss refl = cong-app ss x
cong-sub {Γ} {Δ} {σ} {σ′} {A} {ƛ M} ss refl =
   cong ƛ_ (cong-sub {σ = exts σ}{σ′ = exts σ′} {M = M} (cong-exts ss) refl)
cong-sub {Γ} {Δ} {σ} {σ′} {A} {L · M} ss refl =
   cong₂ _·_ (cong-sub {M = L} ss refl) (cong-sub {M = M} ss refl)

cong-sub-zero : ∀{Γ}{B : Type}{M M′ : Γ ⊢ B}
  → M ≡ M′
    -----------------------------------------
  → ∀{A} → subst-zero M ≡ (subst-zero M′) {A}
cong-sub-zero {Γ}{B}{M}{M′} mm' {A} =
   extensionality λ x → cong (λ z → subst-zero z x) mm'

cong-cons : ∀{Γ Δ}{A}{M N : Δ ⊢ A}{σ τ : Subst Γ Δ}
  → M ≡ N  →  (∀{A} → σ {A} ≡ τ {A})
    --------------------------------
  → ∀{A} → (M • σ) {A} ≡ (N • τ) {A}
cong-cons{Γ}{Δ}{A}{M}{N}{σ}{τ} refl st {A′} = extensionality lemma
  where
  lemma : (x : Γ , A ∋ A′) → (M • σ) x ≡ (M • τ) x
  lemma Z = refl
  lemma (S x) = cong-app st x

cong-seq : ∀{Γ Δ Σ}{σ σ′ : Subst Γ Δ}{τ τ′ : Subst Δ Σ}
  → (∀{A} → σ {A} ≡ σ′ {A}) → (∀{A} → τ {A} ≡ τ′ {A})
  → ∀{A} → (σ ⨟ τ) {A} ≡ (σ′ ⨟ τ′) {A}
cong-seq {Γ}{Δ}{Σ}{σ}{σ′}{τ}{τ′} ss' tt' {A} = extensionality lemma
  where
  lemma : (x : Γ ∋ A) → (σ ⨟ τ) x ≡ (σ′ ⨟ τ′) x
  lemma x =
     begin
       (σ ⨟ τ) x
     ≡⟨⟩
       subst τ (σ x)
     ≡⟨ cong (subst τ) (cong-app ss' x) ⟩
       subst τ (σ′ x)
     ≡⟨ cong-sub{M = σ′ x} tt' refl ⟩
       subst τ′ (σ′ x)
     ≡⟨⟩
       (σ′ ⨟ τ′) x
     ∎

ren-ext : ∀ {Γ Δ}{B C : Type} {ρ : Rename Γ Δ}
        → ren (ext ρ {B = B}) ≡ exts (ren ρ) {C}
ren-ext {Γ}{Δ}{B}{C}{ρ} = extensionality λ x → lemma {x = x}
  where
  lemma : ∀ {x : Γ , B ∋ C} → (ren (ext ρ)) x ≡ exts (ren ρ) x
  lemma {x = Z} = refl
  lemma {x = S x} = refl

rename-subst-ren : ∀ {Γ Δ}{A} {ρ : Rename Γ Δ}{M : Γ ⊢ A}
                 → rename ρ M ≡ ⟪ ren ρ ⟫ M
rename-subst-ren {M = ` x} = refl
rename-subst-ren {ρ = ρ}{M = ƛ N} =
  begin
      rename ρ (ƛ N)
    ≡⟨⟩
      ƛ rename (ext ρ) N
    ≡⟨ cong ƛ_ (rename-subst-ren {ρ = ext ρ}{M = N}) ⟩
      ƛ ⟪ ren (ext ρ) ⟫ N
    ≡⟨ cong ƛ_ (cong-sub {M = N} ren-ext refl) ⟩
      ƛ ⟪ exts (ren ρ) ⟫  N
    ≡⟨⟩
      ⟪ ren ρ ⟫ (ƛ N)
  ∎
rename-subst-ren {M = L · M} = cong₂ _·_ rename-subst-ren rename-subst-ren

ren-shift : ∀{Γ}{A}{B}
          → ren S_ ≡ ↑ {A = B} {A}
ren-shift {Γ}{A}{B} = extensionality λ x → lemma {x = x}
  where
  lemma : ∀ {x : Γ ∋ A} → ren (S_{B = B}) x ≡ ↑ {A = B} x
  lemma {x = Z} = refl
  lemma {x = S x} = refl

rename-shift : ∀{Γ} {A} {B} {M : Γ ⊢ A}
             → rename (S_{B = B}) M ≡ ⟪ ↑ ⟫ M
rename-shift{Γ}{A}{B}{M} =
  begin
    rename S_ M
  ≡⟨ rename-subst-ren ⟩
    ⟪ ren S_ ⟫ M
  ≡⟨ cong-sub{M = M} ren-shift refl ⟩
    ⟪ ↑ ⟫ M
  ∎

exts-cons-shift : ∀{Γ Δ} {A B} {σ : Subst Γ Δ}
                → exts σ {A} {B} ≡ (` Z • (σ ⨟ ↑))
exts-cons-shift = extensionality λ x → lemma{x = x}
  where
  lemma : ∀{Γ Δ} {A B} {σ : Subst Γ Δ} {x : Γ , B ∋ A}
                  → exts σ x ≡ (` Z • (σ ⨟ ↑)) x
  lemma {x = Z} = refl
  lemma {x = S y} = rename-subst-ren

ext-cons-Z-shift : ∀{Γ Δ} {ρ : Rename Γ Δ}{A}{B}
                 → ren (ext ρ {B = B}) ≡ (` Z • (ren ρ ⨟ ↑)) {A}
ext-cons-Z-shift {Γ}{Δ}{ρ}{A}{B} =
  begin
    ren (ext ρ)
  ≡⟨ ren-ext ⟩
    exts (ren ρ)
  ≡⟨ exts-cons-shift{σ = ren ρ} ⟩
   ((` Z) • (ren ρ ⨟ ↑))
  ∎

subst-Z-cons-ids : ∀{Γ}{A B : Type}{M : Γ ⊢ B}
                 → subst-zero M ≡ (M • ids) {A}
subst-Z-cons-ids = extensionality λ x → lemma {x = x}
  where
  lemma : ∀{Γ}{A B : Type}{M : Γ ⊢ B}{x : Γ , B ∋ A}
                      → subst-zero M x ≡ (M • ids) x
  lemma {x = Z} = refl
  lemma {x = S x} = refl

sub-abs : ∀{Γ Δ} {σ : Subst Γ Δ} {N : Γ , ★ ⊢ ★}
        → ⟪ σ ⟫ (ƛ N) ≡ ƛ ⟪ (` Z) • (σ ⨟ ↑) ⟫ N
sub-abs {σ = σ}{N = N} =
   begin
     ⟪ σ ⟫ (ƛ N)
   ≡⟨⟩
     ƛ ⟪ exts σ ⟫ N
   ≡⟨ cong ƛ_ (cong-sub{M = N} exts-cons-shift refl) ⟩
     ƛ ⟪ (` Z) • (σ ⨟ ↑) ⟫ N
   ∎

exts-ids : ∀{Γ}{A B}
         → exts ids ≡ ids {Γ , B} {A}
exts-ids {Γ}{A}{B} = extensionality lemma
  where lemma : (x : Γ , B ∋ A) → exts ids x ≡ ids x
        lemma Z = refl
        lemma (S x) = refl

sub-id : ∀{Γ} {A} {M : Γ ⊢ A}
         → ⟪ ids ⟫ M ≡ M
sub-id {M = ` x} = refl
sub-id {M = ƛ N} =
   begin
     ⟪ ids ⟫ (ƛ N)
   ≡⟨⟩
     ƛ ⟪ exts ids ⟫ N
   ≡⟨ cong ƛ_ (cong-sub{M = N} exts-ids refl)  ⟩
     ƛ ⟪ ids ⟫ N
   ≡⟨ cong ƛ_ sub-id ⟩
     ƛ N
   ∎
sub-id {M = L · M} = cong₂ _·_ sub-id sub-id

rename-id : ∀ {Γ}{A} {M : Γ ⊢ A}
  → rename (λ {A} x → x) M ≡ M
rename-id {M = M} =
   begin
     rename (λ {A} x → x) M
   ≡⟨ rename-subst-ren  ⟩
     ⟪ ren (λ {A} x → x) ⟫ M
   ≡⟨⟩
     ⟪ ids ⟫ M
   ≡⟨ sub-id  ⟩
     M
   ∎

sub-idR : ∀{Γ Δ} {σ : Subst Γ Δ} {A}
       → (σ ⨟ ids) ≡ σ {A}
sub-idR {Γ}{σ = σ}{A} =
          begin
            σ ⨟ ids
          ≡⟨⟩
            ⟪ ids ⟫ ∘ σ
          ≡⟨ extensionality (λ x → sub-id) ⟩
            σ
          ∎

compose-ext : ∀{Γ Δ Σ}{ρ : Rename Δ Σ} {ρ′ : Rename Γ Δ} {A B}
            → ((ext ρ) ∘ (ext ρ′)) ≡ ext (ρ ∘ ρ′) {B} {A}
compose-ext = extensionality λ x → lemma {x = x}
  where
  lemma : ∀{Γ Δ Σ}{ρ : Rename Δ Σ} {ρ′ : Rename Γ Δ} {A B} {x : Γ , B ∋ A}
              → ((ext ρ) ∘ (ext ρ′)) x ≡ ext (ρ ∘ ρ′) x
  lemma {x = Z} = refl
  lemma {x = S x} = refl

compose-rename : ∀{Γ Δ Σ}{A}{M : Γ ⊢ A}{ρ : Rename Δ Σ}{ρ′ : Rename Γ Δ}
  → rename ρ (rename ρ′ M) ≡ rename (ρ ∘ ρ′) M
compose-rename {M = ` x} = refl
compose-rename {Γ}{Δ}{Σ}{A}{ƛ N}{ρ}{ρ′} = cong ƛ_ G
  where
  G : rename (ext ρ) (rename (ext ρ′) N) ≡ rename (ext (ρ ∘ ρ′)) N
  G =
      begin
        rename (ext ρ) (rename (ext ρ′) N)
      ≡⟨ compose-rename{ρ = ext ρ}{ρ′ = ext ρ′} ⟩
        rename ((ext ρ) ∘ (ext ρ′)) N
      ≡⟨ cong-rename compose-ext ⟩
        rename (ext (ρ ∘ ρ′)) N
      ∎
compose-rename {M = L · M} = cong₂ _·_ compose-rename compose-rename

commute-subst-rename : ∀{Γ Δ}{M : Γ ⊢ ★}{σ : Subst Γ Δ}
                        {ρ : ∀{Γ} → Rename Γ (Γ , ★)}
     → (∀{x : Γ ∋ ★} → exts σ {B = ★} (ρ x) ≡ rename ρ (σ x))
     → subst (exts σ {B = ★}) (rename ρ M) ≡ rename ρ (subst σ M)
commute-subst-rename {M = ` x} r = r
commute-subst-rename{Γ}{Δ}{ƛ N}{σ}{ρ} r =
   cong ƛ_ (commute-subst-rename{Γ , ★}{Δ , ★}{N}
               {exts σ}{ρ = ρ′} (λ {x} → H {x}))
   where
   ρ′ : ∀ {Γ} → Rename Γ (Γ , ★)
   ρ′ {∅} = λ ()
   ρ′ {Γ , ★} = ext ρ

   H : {x : Γ , ★ ∋ ★} → exts (exts σ) (ext ρ x) ≡ rename (ext ρ) (exts σ x)
   H {Z} = refl
   H {S y} =
     begin
       exts (exts σ) (ext ρ (S y))
     ≡⟨⟩
       rename S_ (exts σ (ρ y))
     ≡⟨ cong (rename S_) r ⟩
       rename S_ (rename ρ (σ y))
     ≡⟨ compose-rename ⟩
       rename (S_ ∘ ρ) (σ y)
     ≡⟨ cong-rename refl ⟩
       rename ((ext ρ) ∘ S_) (σ y)
     ≡⟨ sym compose-rename ⟩
       rename (ext ρ) (rename S_ (σ y))
     ≡⟨⟩
       rename (ext ρ) (exts σ (S y))
     ∎
commute-subst-rename {M = L · M}{ρ = ρ} r =
   cong₂ _·_ (commute-subst-rename{M = L}{ρ = ρ} r)
             (commute-subst-rename{M = M}{ρ = ρ} r)

exts-seq : ∀{Γ Δ Δ′} {σ₁ : Subst Γ Δ} {σ₂ : Subst Δ Δ′}
         → ∀ {A} → (exts σ₁ ⨟ exts σ₂) {A} ≡ exts (σ₁ ⨟ σ₂)
exts-seq = extensionality λ x → lemma {x = x}
  where
  lemma : ∀{Γ Δ Δ′}{A}{x : Γ , ★ ∋ A} {σ₁ : Subst Γ Δ}{σ₂ : Subst Δ Δ′}
     → (exts σ₁ ⨟ exts σ₂) x ≡ exts (σ₁ ⨟ σ₂) x
  lemma {x = Z} = refl
  lemma {A = ★}{x = S x}{σ₁}{σ₂} =
     begin
       (exts σ₁ ⨟ exts σ₂) (S x)
     ≡⟨⟩
       ⟪ exts σ₂ ⟫ (rename S_ (σ₁ x))
     ≡⟨ commute-subst-rename{M = σ₁ x}{σ = σ₂}{ρ = S_} refl ⟩
       rename S_ (⟪ σ₂ ⟫ (σ₁ x))
     ≡⟨⟩
       rename S_ ((σ₁ ⨟ σ₂) x)
     ∎

sub-sub : ∀{Γ Δ Σ}{A}{M : Γ ⊢ A} {σ₁ : Subst Γ Δ}{σ₂ : Subst Δ Σ}
            → ⟪ σ₂ ⟫ (⟪ σ₁ ⟫ M) ≡ ⟪ σ₁ ⨟ σ₂ ⟫ M
sub-sub {M = ` x} = refl
sub-sub {Γ}{Δ}{Σ}{A}{ƛ N}{σ₁}{σ₂} =
   begin
     ⟪ σ₂ ⟫ (⟪ σ₁ ⟫ (ƛ N))
   ≡⟨⟩
     ƛ ⟪ exts σ₂ ⟫ (⟪ exts σ₁ ⟫ N)
   ≡⟨ cong ƛ_ (sub-sub{M = N}{σ₁ = exts σ₁}{σ₂ = exts σ₂}) ⟩
     ƛ ⟪ exts σ₁ ⨟ exts σ₂ ⟫ N
   ≡⟨ cong ƛ_ (cong-sub{M = N} (λ {A} → exts-seq) refl) ⟩
     ƛ ⟪ exts ( σ₁ ⨟ σ₂) ⟫ N
   ∎
sub-sub {M = L · M} = cong₂ _·_ (sub-sub{M = L}) (sub-sub{M = M})

rename-subst : ∀{Γ Δ Δ′}{M : Γ ⊢ ★}{ρ : Rename Γ Δ}{σ : Subst Δ Δ′}
             → ⟪ σ ⟫ (rename ρ M) ≡ ⟪ σ ∘ ρ ⟫ M
rename-subst {Γ}{Δ}{Δ′}{M}{ρ}{σ} =
   begin
     ⟪ σ ⟫ (rename ρ M)
   ≡⟨ cong ⟪ σ ⟫ (rename-subst-ren{M = M}) ⟩
     ⟪ σ ⟫ (⟪ ren ρ ⟫ M)
   ≡⟨ sub-sub{M = M} ⟩
     ⟪ ren ρ ⨟ σ ⟫ M
   ≡⟨⟩
     ⟪ σ ∘ ρ ⟫ M
   ∎

sub-assoc : ∀{Γ Δ Σ Ψ : Context} {σ : Subst Γ Δ} {τ : Subst Δ Σ}
             {θ : Subst Σ Ψ}
          → ∀{A} → (σ ⨟ τ) ⨟ θ ≡ (σ ⨟ τ ⨟ θ) {A}
sub-assoc {Γ}{Δ}{Σ}{Ψ}{σ}{τ}{θ}{A} = extensionality λ x → lemma{x = x}
  where
  lemma : ∀ {x : Γ ∋ A} → ((σ ⨟ τ) ⨟ θ) x ≡ (σ ⨟ τ ⨟ θ) x
  lemma {x} =
      begin
        ((σ ⨟ τ) ⨟ θ) x
      ≡⟨⟩
        ⟪ θ ⟫ (⟪ τ ⟫ (σ x))
      ≡⟨ sub-sub{M = σ x} ⟩
        ⟪ τ ⨟ θ ⟫ (σ x)
      ≡⟨⟩
        (σ ⨟ τ ⨟ θ) x
      ∎

subst-zero-exts-cons : ∀{Γ Δ}{σ : Subst Γ Δ}{B}{M : Δ ⊢ B}{A}
                     → exts σ ⨟ subst-zero M ≡ (M • σ) {A}
subst-zero-exts-cons {Γ}{Δ}{σ}{B}{M}{A} =
    begin
      exts σ ⨟ subst-zero M
    ≡⟨ cong-seq exts-cons-shift subst-Z-cons-ids ⟩
      (` Z • (σ ⨟ ↑)) ⨟ (M • ids)
    ≡⟨ sub-dist ⟩
      (⟪ M • ids ⟫ (` Z)) • ((σ ⨟ ↑) ⨟ (M • ids))
    ≡⟨ cong-cons (sub-head{σ = ids}) refl ⟩
      M • ((σ ⨟ ↑) ⨟ (M • ids))
    ≡⟨ cong-cons refl (sub-assoc{σ = σ}) ⟩
      M • (σ ⨟ (↑ ⨟ (M • ids)))
    ≡⟨ cong-cons refl (cong-seq{σ = σ} refl (sub-tail{M = M}{σ = ids})) ⟩
      M • (σ ⨟ ids)
    ≡⟨ cong-cons refl (sub-idR{σ = σ}) ⟩
      M • σ
    ∎

subst-commute : ∀{Γ Δ}{N : Γ , ★ ⊢ ★}{M : Γ ⊢ ★}{σ : Subst Γ Δ }
    → ⟪ exts σ ⟫ N [ ⟪ σ ⟫ M ] ≡ ⟪ σ ⟫ (N [ M ])
subst-commute {Γ}{Δ}{N}{M}{σ} =
     begin
       ⟪ exts σ ⟫ N [ ⟪ σ ⟫ M ]
     ≡⟨⟩
       ⟪ subst-zero (⟪ σ ⟫ M) ⟫ (⟪ exts σ ⟫ N)
     ≡⟨ cong-sub {M = ⟪ exts σ ⟫ N} subst-Z-cons-ids refl ⟩
       ⟪ ⟪ σ ⟫ M • ids ⟫ (⟪ exts σ ⟫ N)
     ≡⟨ sub-sub {M = N} ⟩
       ⟪ (exts σ) ⨟ ((⟪ σ ⟫ M) • ids) ⟫ N
     ≡⟨ cong-sub {M = N} (cong-seq exts-cons-shift refl) refl ⟩
       ⟪ (` Z • (σ ⨟ ↑)) ⨟ (⟪ σ ⟫ M • ids) ⟫ N
     ≡⟨ cong-sub {M = N} (sub-dist {M = ` Z}) refl ⟩
       ⟪ ⟪ ⟪ σ ⟫ M • ids ⟫ (` Z) • ((σ ⨟ ↑) ⨟ (⟪ σ ⟫ M • ids)) ⟫ N
     ≡⟨⟩
       ⟪ ⟪ σ ⟫ M • ((σ ⨟ ↑) ⨟ (⟪ σ ⟫ M • ids)) ⟫ N
     ≡⟨ cong-sub{M = N} (cong-cons refl (sub-assoc{σ = σ})) refl ⟩
       ⟪ ⟪ σ ⟫ M • (σ ⨟ ↑ ⨟ ⟪ σ ⟫ M • ids) ⟫ N
     ≡⟨ cong-sub{M = N} refl refl ⟩
       ⟪ ⟪ σ ⟫ M • (σ ⨟ ids) ⟫ N
     ≡⟨ cong-sub{M = N} (cong-cons refl (sub-idR{σ = σ})) refl ⟩
       ⟪ ⟪ σ ⟫ M • σ ⟫ N
     ≡⟨ cong-sub{M = N} (cong-cons refl (sub-idL{σ = σ})) refl ⟩
       ⟪ ⟪ σ ⟫ M • (ids ⨟ σ) ⟫ N
     ≡⟨ cong-sub{M = N} (sym sub-dist) refl ⟩
       ⟪ M • ids ⨟ σ ⟫ N
     ≡⟨ sym (sub-sub{M = N}) ⟩
       ⟪ σ ⟫ (⟪ M • ids ⟫ N)
     ≡⟨ cong ⟪ σ ⟫ (sym (cong-sub{M = N} subst-Z-cons-ids refl)) ⟩
       ⟪ σ ⟫ (N [ M ])
     ∎

rename-subst-commute : ∀{Γ Δ}{N : Γ , ★ ⊢ ★}{M : Γ ⊢ ★}{ρ : Rename Γ Δ }
    → (rename (ext ρ) N) [ rename ρ M ] ≡ rename ρ (N [ M ])
rename-subst-commute {Γ}{Δ}{N}{M}{ρ} =
     begin
       (rename (ext ρ) N) [ rename ρ M ]
     ≡⟨ cong-sub (cong-sub-zero (rename-subst-ren{M = M}))
                 (rename-subst-ren{M = N}) ⟩
       (⟪ ren (ext ρ) ⟫ N) [ ⟪ ren ρ ⟫ M ]
     ≡⟨ cong-sub refl (cong-sub{M = N} ren-ext refl) ⟩
       (⟪ exts (ren ρ) ⟫ N) [ ⟪ ren ρ ⟫ M ]
     ≡⟨ subst-commute{N = N} ⟩
       subst (ren ρ) (N [ M ])
     ≡⟨ sym (rename-subst-ren) ⟩
       rename ρ (N [ M ])
     ∎

_〔_〕 : ∀ {Γ A B C}
        → Γ , B , C ⊢ A
        → Γ ⊢ B
          ---------
        → Γ , C ⊢ A
_〔_〕 {Γ} {A} {B} {C} N M =
   subst {Γ , B , C} {Γ , C} (exts (subst-zero M)) {A} N

substitution : ∀{Γ}{M : Γ , ★ , ★ ⊢ ★}{N : Γ , ★ ⊢ ★}{L : Γ ⊢ ★}
    → (M [ N ]) [ L ] ≡ (M 〔 L 〕) [ (N [ L ]) ]
substitution{M = M}{N = N}{L = L} =
   sym (subst-commute{N = M}{M = N}{σ = subst-zero L})

{- ## Unicode

This chapter uses the following unicode:

    ⟪  U+27EA  MATHEMATICAL LEFT DOUBLE ANGLE BRACKET (\<<)
    ⟫  U+27EA  MATHEMATICAL RIGHT DOUBLE ANGLE BRACKET (\>>)
    ↑  U+2191  UPWARDS ARROW (\u)
    •  U+2022  BULLET (\bub)
    ⨟  U+2A1F  Z NOTATION SCHEMA COMPOSITION (C-x 8 RET Z NOTATION SCHEMA COMPOSITION)
    〔  U+3014  LEFT TORTOISE SHELL BRACKET (\( option 9 on page 2)
    〕  U+3015  RIGHT TORTOISE SHELL BRACKET (\) option 9 on page 2) -}   