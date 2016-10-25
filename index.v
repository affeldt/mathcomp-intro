Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun eqtype ssrnat seq choice fintype.
From mathcomp
Require Import div path bigop prime finset fingroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** tentative formalization of the theorem V.3.1 of
    [Arnaudies&Fraysse]
    Arnaudies, J.M., Fraysse, H.: Cours de mathematiques 1, Algebre, Dunod Universite, 1987

    to illustrate the Mathematiques Components library
*)

(** Sect. 2: Basics of Coq *)

Lemma andC :
  forall P Q : Prop, P /\ Q -> Q /\ P.
Proof.
move=> P Q.
by case.
Show Proof.
(*exact (fun P Q PandQ => match PandQ with
  conj p q => conj q p end).*)
Qed.

Lemma andbC :
  forall P Q : bool, andb P Q = true -> andb Q P = true.
Proof.
case.
- by case.
- by case.
(*exact (fun P Q => match P with
| true => match Q with
          | true => id
          | false => id
          end
| false => match Q with
          | true => id
          | false => id
          end
      end).*)
Qed.

(** Sect. 5: Overview of Finite Groups *)

Local Open Scope group_scope.

Module Sect5.
Section sect5.

Variable gT : finGroupType.
Variables G : {group gT}.
Variables g h : gT.
Hypotheses (gG : g \in G) (hG : h \in G).
Check g * h : gT.
Check groupM gG hG : g * h \in G.

End sect5.
End Sect5.

Section coset_bijection.

Variable gT : finGroupType.
Variables G H : {group gT}.
Hypothesis HG : H \subset G.

(** Sect. 6: Left-cosets are disjoint *)

Lemma coset_disjoint L0 L1 :
  L0 \in lcosets H G ->
  L1 \in lcosets H G ->
  L0 :&: L1 != set0 -> L0 = L1.
Proof.
case/lcosetsP => g0 g0G ->{L0}.
case/lcosetsP => g1 g1G ->{L1}.
move=> g0_g1_disj.
apply/lcoset_eqP.
case/set0Pn : g0_g1_disj => /= g.
rewrite in_setI => /andP[].
rewrite 3!mem_lcoset => g_g0 g_g1.
rewrite -(mul1g g0).
rewrite -(mulgV g).
rewrite 2!mulgA.
rewrite -mulgA.
rewrite groupM //.
rewrite groupVl //.
rewrite invMg.
by rewrite invgK.
Qed.

(** Sect. 7: Injection into the set of left-cosets *)

Definition reprs := repr @: lcosets H G.

Lemma mem_repr_coset x : x \in G -> repr (x *: H) \in G.
Proof.
move=> xG.
rewrite /repr.
case: ifPn => // x1.
case: pickP => /=.
  move=> g0.
  case/lcosetP => g1 g1H ->.
  rewrite groupM //.
  by move/subsetP : (HG); apply.
move/(_ x).
by rewrite lcoset_refl.
Qed.

Lemma repr_form x : x \in G -> repr (x *: H) *: H = x *: H.
Proof.
move=> xG.
apply coset_disjoint.
- apply/lcosetsP.
  exists (repr (x *: H)) => //.
  by apply mem_repr_coset.
- apply/lcosetsP.
  by exists x.
- apply/set0Pn => /=.
  exists (repr (x *: H)) => //.
  rewrite in_setI.
  rewrite lcoset_refl /=.
  rewrite (mem_repr x) //.
  by rewrite lcoset_refl.
Qed.

Lemma reprs_subset : reprs \subset G.
Proof.
apply/subsetP => g.
case/imsetP => /= gs.
case/lcosetsP => g' g'H ->{gs} ->{g}.
by rewrite mem_repr_coset.
Qed.

Lemma injective_coset :
  {in reprs &, injective (fun g => g *: H)}.
Proof.
move=> /= g g' /imsetP[] /= L LHG gL.
move=> /imsetP[] /= K KHG g'K abs.
suff : L = K.
  move=> LK.
  rewrite LK in gL.
  by rewrite gL g'K.
case/lcosetsP : LHG => g0 g0G g0L.
rewrite {}g0L {L} in gL *.
case/lcosetsP : KHG => g1 g1G g1K.
rewrite {}g1K {K} in g'K *.
have <- : g *: H = g0 *: H.
  apply coset_disjoint.
  - apply/lcosetsP.
    exists g => //.
    by rewrite gL mem_repr_coset.
  - apply/lcosetsP.
    by exists g0.
  - apply/set0Pn.
    exists (repr (g0 *: H)).
    by rewrite !inE -gL lcoset_refl /= gL (mem_repr g0) // lcoset_refl.
suff : g' *: H = g1 *: H.
  by move=> <-.
apply coset_disjoint => //.
- apply/lcosetsP.
  exists g' => //.
  by rewrite g'K mem_repr_coset.
- apply/lcosetsP.
  by exists g1.
- apply/set0Pn.
  exists (repr (g1 *: H)).
  by rewrite inE -g'K lcoset_refl /= g'K (mem_repr g1) // lcoset_refl.
Qed.

Lemma surjective_coset : (fun x => x *: H) @: reprs = lcosets H G.
Proof.
apply/eqP.
rewrite eqEsubset.
apply/andP; split.
- apply/subsetP => i.
  case/imsetP => g.
  case/imsetP => L HL ->{g} ->{i}.
  apply/lcosetsP.
  exists (repr L) => //.
  case/lcosetsP : HL => x xG ->.
  by apply mem_repr_coset.
- apply/subsetP => i.
  case/lcosetsP => x xG ->{i}.
  apply/imsetP.
  exists (repr (x *: H)).
    rewrite /reprs.
    apply/imsetP.
    exists (x *: H) => //.
    apply/lcosetsP.
    by exists x.
  by rewrite repr_form.
Qed.

End coset_bijection.

(** Sect. 8: Transitivity of the group index *)

Notation "#| G : H |" := #| lcosets H G |.

Section index.

Variable gT : finGroupType.
Variables G H K : {group gT}.
Hypotheses (HG : H \subset G) (KG : K \subset G) (HK : K \proper H).

Lemma index_trans : #| G : K | = (#| G : H | * #| H : K |)%nat.
Proof.
rewrite /=.
set calG := reprs G H.
have calG_H_inj : {in calG &, injective (fun x => x *: H)}.
  by apply: injective_coset HG.
set calH := reprs H K.
have calH_K_inj : {in calH &, injective (fun x=> x *: K)}.
  apply: injective_coset.
  by move/proper_sub : HK.
pose phi := fun gh : gT * gT => let: (g, h) := gh in (g * h) *: K.
(* [Arnaudies&Fraysse] injectivite de phi:
   Si ghK = g'h'K avec g, g' \in calG et h, h' \in calH,
   on en deduit g'^-1ghK = h'K \proper H.
   Donc g'^-1gH \cap H n'est pas vide puisque h'K \proper H
   et h'K \proper g'^-1gH, et puisque g'^-1gH et H sont deux classes
   a gauche mod (H), necessairement g'^-1gH = H, d'ou gH = g'H,
   d'ou g = g' puisque alpha est bijective.
   On en deduit: hK = h'K, d'ou h = h' puisque beta est bijective,
   et finalement (g,h)=(g'.h'). *)
have phi_injective : {in setX calG calH & , injective phi}.
  case => g h.
  rewrite inE /=.
  case => g' h' /andP[gG hH].
  rewrite /phi inE /= => /andP[g'G h'H] ghK.
  have step1 : (g'^-1 * g * h) *: K = h' *: K.
    move: ghK.
    move/(congr1 (fun X => g'^-1 *: X)).
    by rewrite -2!lcosetM !mulgA mulVg mul1g.
  have step2 : h' *: K \proper H.
    apply/properP; split.
      apply/subsetP => x.
      case/lcosetP => x0 Hx0 ->.
      rewrite groupM //.
        by move/proper_sub : (HK) => /reprs_subset /subsetP; apply.
      move/proper_sub : HK => /subsetP; by apply.
    case/properP : HK => HK' [x xH xK].
    exists (h' * x) => //.
    rewrite groupM //.
      by move/proper_sub : (HK) => /reprs_subset /subsetP; apply.
    apply: contra xK.
    case/lcosetP => x0 x0K.
    by move/mulgI => ->.
  have {step2}step3 : (g'^-1 * g *: H) :&: H != set0.
    have step3 : h' *: K \proper (g'^-1 * g) *: H.
      rewrite -step1.
      apply/properP; split.
        rewrite sub_lcoset -lcosetM mulgA mulVg mul1g.
        apply/subsetP => x.
        case/lcosetP => x0 x0K ->.
        rewrite groupM //.
          by move/proper_sub : (HK) => /reprs_subset /subsetP; apply.
        by move/proper_sub : HK => /subsetP; apply.
      case/properP : HK => HK' [x xH xK].
      exists ((g'^-1 * g) * (h * x)) => //.
        rewrite mem_lcoset mulgA mulVg mul1g groupM //.
        by move/proper_sub : (HK) => /reprs_subset /subsetP; apply.
      rewrite mem_lcoset -(mulgA g'^-1 g (h * x)) (mulgA g h x).
      by rewrite (mulgA g'^-1 (g * h) x) (mulgA g'^-1 g h) mulgA mulVg mul1g.
    apply/set0Pn; exists h'.
    rewrite in_setI.
    apply/andP; split.
      move/proper_sub/subsetP : step3; apply.
      by rewrite mem_lcoset mulVg group1.
    move/proper_sub/subsetP : step2; apply.
    by rewrite mem_lcoset mulVg group1.
  have {step3}step4 : (g'^-1 * g) *: H = H.
    case/set0Pn : step3 => x.
    rewrite in_setI.
    case/andP.
    case/lcosetP => x0 Hx0 -> Htmp.
    rewrite lcoset_id //.
    by rewrite -(mulg1 g) -(mulgV x0) !mulgA groupM // groupVl // invgK.
  have {step4}step5 : g *: H = g' *: H.
    by rewrite -{2}step4 -lcosetM mulgA mulgV mul1g.
  have {step5}step6 : g = g'.
    by apply calG_H_inj.
  have step7 : h *: K = h' *: K.
    by rewrite -step1 step6 mulVg mul1g.
  have {step7}step8 : h = h'.
    by apply calH_K_inj.
  by rewrite step6 step8.
have calG_H_surj : (fun x => x *: H) @: calG = lcosets H G.
  by apply surjective_coset.
have calH_K_surj : (fun x => x *: K) @: calH = lcosets K H.
  apply surjective_coset.
  by move/proper_sub : (HK); apply.
(* [Arnaudies&Fraysse] surjectivite de phi:
   Soit l \in calG; alors lH \in (G/H)_g.
   On a donc un g \in calG tel que lH = gH;
   alors g^-1lH = H, donc g^-1l \in H.
   On a donc un h \in calH tel que g^-1lK = hK.
   On en deduit lK = ghK = phi(g, h). *)
have phi_surjective : phi @: (setX calG calH) = lcosets K G.
  apply/eqP.
  rewrite eqEsubset.
  apply/andP; split; apply/subsetP => i.
    case/imsetP => /=; case=> [x1 x2].
    rewrite !inE /= => /andP[Hx1 Hx2] ->{i}.
    apply/lcosetsP.
    exists (x1 * x2) => //.
    rewrite groupM //.
      by move : (HG) => /reprs_subset /subsetP; apply.
    move/subsetP : HG; apply.
    apply/subsetP: x2 Hx2.
    by apply/reprs_subset/proper_sub.
  case/lcosetsP => l lG ->{i}.
  apply/imsetP => /=.
  have [g [gcalG gHlH]] : exists g, g \in calG /\ g *: H = l *: H.
    exists (repr (l *: H)).
    split.
      apply/imsetP.
      exists (l *: H) => //.
      apply/lcosetsP.
      by exists l.
    by rewrite (repr_form HG).
  have step1 : (g^-1 * l) *: H = H.
    move/(congr1 (fun x => g^-1 *: x)) : gHlH.
    by rewrite -!lcosetM mulVg lcoset1.
  have {step1}step2 : g^-1 * l \in H.
    by rewrite -step1 lcoset_refl.
  have [h [hcalH glKhK]] : exists h, h \in calH /\ (g^-1 * l) *: K = h *: K.
    exists (repr ((g^-1 * l) *: K)).
    split.
      apply/imsetP.
      exists ((g^-1 * l) *: K) => //.
      apply/lcosetsP.
      by exists (g^-1 * l).
    rewrite (repr_form KG) // groupM // groupVl // invgK //.
    by move: (reprs_subset HG) => /subsetP; apply.
  exists (g, h).
    by rewrite in_setX gcalG.
  move/(congr1 (fun x => g *: x)) : glKhK.
  by rewrite -!lcosetM mulgA mulgV mul1g => ->.
rewrite -phi_surjective -calG_H_surj -calH_K_surj.
rewrite (card_in_imset phi_injective) cardsX.
by rewrite (card_in_imset calG_H_inj) (card_in_imset calH_K_inj).
Qed.

End index.

(* Sect. 9: Lagrange Theorem *)

Section lagrange.

Variable gT : finGroupType.
Variables G H : {group gT}.
Hypotheses (HG : H \subset G).

Lemma coset1 g : g *: (1%G : {group gT}) = [set g].
Proof.
apply/eqP; rewrite eqEsubset; apply/andP; split; apply/subsetP => j.
  case/lcosetP => x.
  rewrite !inE => /eqP ->.
  by rewrite mulg1 => /eqP.
rewrite in_set1 => /eqP ->.
apply/lcosetP.
exists 1 => //.
by rewrite mulg1.
Qed.

Lemma lcosets1 (K : {group gT}) : lcosets 1%G K = (set1) @: K.
Proof.
apply/eqP; rewrite eqEsubset; apply/andP; split; apply/subsetP => i.
  case/lcosetsP => g gK ->{i}.
  apply/imsetP.
  exists g => //.
  by apply coset1.
case/imsetP => g gK ->{i}.
apply/lcosetsP.
exists g => //.
by rewrite coset1.
Qed.

Theorem Lagrange : #| G | = (#| H | * #| G : H |)%nat.
Proof.
case/boolP : (1%G \proper H) => H1; last first.
  suff -> : H = 1%G.
    rewrite cards1 mul1n lcosets1 // card_imset //.
    exact: set1_inj.
  apply/trivGP.
  move: H1.
  by rewrite proper1G negbK => /eqP ->.
have G1 : 1%G \subset G.
  apply/subsetP => h.
  by rewrite inE => /eqP ->.
move: (index_trans HG G1 H1).
rewrite lcosets1 (card_imset _ set1_inj).
rewrite mulnC lcosets1 card_imset //.
exact: set1_inj.
Qed.

End lagrange.
