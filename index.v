Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun eqtype ssrnat seq choice fintype.
From mathcomp
Require Import div path bigop prime finset fingroup.

Local Open Scope group_scope.

Section coset_bijection.

Variable gT : finGroupType.
Variables G H : {group gT}.
Hypothesis (HG : H \subset G).

Definition dom : {set gT} := repr @: lcosets H G.

Lemma dom_in_G : dom \subset G.
Proof.
apply/subsetP => g.
case/imsetP => /= gs.
case/lcosetsP => g' g'H ->{gs} ->{g}.
rewrite /repr.
case: ifP => // abs.
case: pickP => /=.
  move=> g''.
  case/lcosetP => g3 Hg3 ->.
  rewrite groupM => //.
  move/subsetP : HG; by apply.
move/(_ g').
by rewrite lcoset_refl.
Qed.

Lemma same_coset K K' x:
  K \in lcosets H G ->
  K' \in lcosets H G ->
  x \in K -> x \in K' ->         
  K = K'.
Proof.
case/lcosetsP => x0 Hx0 ->.
case/lcosetsP => x1 Hx1 ->.
rewrite 2!mem_lcoset => H1 H2.
apply/lcoset_eqP.
rewrite mem_lcoset.
rewrite -(mul1g x0).
rewrite -(mulgV x).
rewrite 2!mulgA.
rewrite -mulgA.
rewrite groupM //.
rewrite groupVl //.
by rewrite invMg invgK.
Qed.

Lemma mem_repr_coset x : x \in G -> repr (x *: H) \in G.
Proof.
move=> xG.
rewrite /repr.
case: ifP => // x1.
case: pickP => /=.
  move=> x0.
  case/lcosetP => x2 Hx2 ->.
  rewrite groupM //.
  by move/subsetP : (HG); apply.
move/(_ x).
by rewrite lcoset_refl.
Qed.

Lemma injective_quot : {in dom &, injective (fun x => x *: H)}.
Proof.
move=> x x' /imsetP[] /= L LHG xL /imsetP[] /= K KHG x'K abs.
suff : L = K by move=> LK; rewrite LK in xL; rewrite xL x'K.
case/lcosetsP : LHG => x0 x0G x0L; subst L.
case/lcosetsP : KHG => x1 x1G x1K; subst K.
have : x *: H = x0 *: H.
  apply same_coset with x => //.
  apply/lcosetsP.
  exists x => //.
  rewrite xL.
  by apply mem_repr_coset.
  apply/lcosetsP.
  by exists x0.
  by rewrite lcoset_refl.            
  rewrite xL.
  apply mem_repr with x0.
  by rewrite lcoset_refl.
move=> <-.
have : x' *: H = x1 *: H.
  apply same_coset with x' => //.
  apply/lcosetsP.
  exists x' => //.
  rewrite x'K.
  by apply mem_repr_coset.
  apply/lcosetsP.
  by exists x1.
  by rewrite lcoset_refl.            
  rewrite x'K.
  apply mem_repr with x1.
  by rewrite lcoset_refl.
by move=> <-.
Qed.

Lemma repr_form x : x \in G -> x *: H = repr (x *: H) *: H.
Proof.
move=> xG.
apply (same_coset) with (repr (x *: H)).
  apply/lcosetsP.
  by exists x.
  apply/lcosetsP.
  exists (repr (x *: H)) => //.
  by apply mem_repr_coset.
  apply mem_repr with x => //.
  by rewrite lcoset_refl.
  by rewrite lcoset_refl.
Qed.

Lemma surj : (fun x => x *: H) @: dom = lcosets H G.
Proof.
have Htmp : (fun x => x *: H) @: dom \subset lcosets H G.
  apply/subsetP => i.
  case/imsetP => g.
  case/imsetP => L HL ->{g} ->{i}.
  apply/lcosetsP.
  exists (repr L) => //.
  case/lcosetsP : HL => x xG ->.
  by apply mem_repr_coset.
have Htmp' : lcosets H G \subset (fun x => x *: H) @: dom.
  apply/subsetP => i.
  case/lcosetsP => x xG ->{i}.
  apply/imsetP.
  exists (repr (x *: H)).
    rewrite /dom.
    apply/imsetP.
    exists (x *: H) => //.
    apply/lcosetsP.
    by exists x.
by rewrite -repr_form.
apply/eqP.
by rewrite eqEsubset Htmp Htmp'.
Qed.

End coset_bijection.

Section index.

Variable gT : finGroupType.
Variables G H K : {group gT}.
Hypotheses (HG : H \subset G) (KG : K \subset G) (HK : K \proper H).

Lemma index : #| lcosets K G| = (#| lcosets H G| * #| lcosets K H|)%nat.
Proof.
rewrite /=.
set calG := dom _ G H.
have HcalG : {in calG &, injective (fun x => x *: H)}.
  by move: (injective_quot _ _ _ HG).
set calH := dom _ H K.
have HcalH : {in calH &, injective (fun x=> x *: K)}.
  apply injective_quot.
  by move/proper_sub : (HK).
set phi := fun xy : gT * gT => let: (x, y) := xy in (x * y) *: K.
have phi_injective : {in setX calG calH & , injective phi}.
  case => g h.
  rewrite inE /=.
  case => g' h' /andP[gG hH].
  rewrite /phi inE /= => /andP[g'G h'H] ghK.
  have H1 : (g'^-1 * g * h) *: K = h' *: K.
    move/(congr1 (fun x => g'^-1 *: x)) : ghK.
    rewrite -lcosetM mulgA => ->.
    by rewrite -lcosetM mulgA mulVg mul1g.
  have H2 : h' *: K \proper H.
    apply/properP; split.
      apply/subsetP => x.
      case/lcosetP => x0 Hx0 ->.
      rewrite groupM //.
      by move/proper_sub : (HK) => /dom_in_G /subsetP; apply.
      move/proper_sub : HK => /subsetP; by apply.
    case/properP : HK => HK' [x xH xK].
    exists (h' * x) => //.
    rewrite groupM //.
      by move/proper_sub : (HK) => /dom_in_G /subsetP; apply.
    apply: contra xK.
    case/lcosetP => x0 x0K.
    by move/mulgI => ->.
  have H3 : (g'^-1 * g *: H) :&: H != set0.
    have H3'' : h' *: K \proper (g'^-1 * g) *: H. 
      rewrite -H1.
      apply/properP; split.
        rewrite sub_lcoset.
        rewrite -lcosetM.
        rewrite mulgA.
        rewrite mulVg mul1g.
        apply/subsetP => x.
        case/lcosetP => x0 x0K ->.
        rewrite groupM //.
          by move/proper_sub : (HK) => /dom_in_G /subsetP; apply.
        by move/proper_sub : HK => /subsetP; apply.
      case/properP : HK => HK' [x xH xK].
      exists ((g'^-1 * g) * (h * x)) => //.
        rewrite mem_lcoset.
        rewrite mulgA.
        rewrite mulVg.
        rewrite mul1g groupM //.
        by move/proper_sub : (HK) => /dom_in_G /subsetP; apply.
      rewrite mem_lcoset.
      rewrite -(mulgA g'^-1 g (h * x)).
      rewrite (mulgA g h x).
      rewrite (mulgA g'^-1 (g * h) x).
      rewrite (mulgA g'^-1 g h).
      rewrite mulgA.
      by rewrite mulVg mul1g.
    (* use H2 to conclude *)
    apply/set0Pn.
    case/properP : HK => HK' [x xH xK].
    exists h'.
    rewrite in_setI.
    apply/andP; split.
      move/proper_sub/subsetP : H3''.
      apply.
      rewrite mem_lcoset.
      by rewrite mulVg group1.
    by move/proper_sub : (HK) => /dom_in_G /subsetP; apply.
  have H4 : (g'^-1 * g) *: H = H.
    case/set0Pn : H3 => x.
    rewrite in_setI.
    case/andP.
    case/lcosetP => x0 Hx0 -> Htmp.
    rewrite lcoset_id //.
    rewrite -(mulg1 g).
    rewrite -(mulgV x0).
    rewrite !mulgA.
    rewrite groupM //.
    by rewrite groupVl // invgK.
  have H5 : g *: H = g' *: H.
    rewrite -{2}H4.
    rewrite -lcosetM.
    by rewrite mulgA mulgV mul1g.
  have H6 : g = g'.
    by apply HcalG.
  have H7 : h *: K = h' *: K.
    subst g'.
    by rewrite mulVg mul1g in H1.
  have H8 : h = h'.
    by apply HcalH.
  by rewrite H6 H8.
have surj1 : (fun x => x *: H) @: calG = lcosets H G.
  by apply surj.
have surj2 : (fun x => x *: K) @: calH = lcosets K H.
  apply surj.
  by move/proper_sub : (HK); apply.
have surj3 : phi @: (setX calG calH) = lcosets K G.
  apply/setP => /= i.
  apply/idP/idP.
    case/imsetP => /=; case=> [x1 x2].
    rewrite !inE /= => /andP[Hx1 Hx2] ->{i}.
    apply/lcosetsP.
    exists (x1 * x2) => //.
    rewrite groupM //.
    by move : (HG) => /dom_in_G /subsetP; apply.
    move/subsetP : HG; apply.
    move : x2 Hx2.
    apply/subsetP.
    by apply/dom_in_G/proper_sub.
  case/lcosetsP => l lG ->{i}.
  apply/imsetP => /=.
  have [g [gcalG Hg]] : exists g, g \in calG /\ g *: H = l *: H.
    exists (repr (l *: H)).
    split.
      apply/imsetP.
      exists (l *: H) => //.
      apply/lcosetsP.
      by exists l.
    by rewrite -(repr_form _ G).
  have H1 : (g^-1 * l) *: H = H.
    move/(congr1 (fun x => g^-1 *: x)) in Hg.
    rewrite -!lcosetM mulVg lcoset1 in Hg.
    done.
  have H2 : g^-1 * l \in H.
    rewrite -H1.
    by rewrite lcoset_refl.
  have [h [hcalH Hh]] : exists h, h \in calH /\ (g^-1 * l) *: K = h *: K.
    exists (repr ((g^-1 * l) *: K)).
    split.
      apply/imsetP.
      exists ((g^-1 * l) *: K) => //.
      apply/lcosetsP.
      by exists (g^-1 * l) => //.
    rewrite -(repr_form _ G) //.
    rewrite groupM //.
    rewrite groupVl // invgK //.
    by move: (dom_in_G _ _ _ HG) => /subsetP; apply.
  exists (g, h).
    by rewrite in_setX gcalG.
  move/(congr1 (fun x => g *: x)) in Hh.
  rewrite -!lcosetM in Hh.
  rewrite /phi.
  rewrite -Hh.
  by rewrite mulgA mulgV mul1g.
rewrite -surj3 -surj1 -surj2.
rewrite (card_in_imset phi_injective).
rewrite cardsX.
rewrite (card_in_imset HcalG).
by rewrite (card_in_imset HcalH).
Qed.

End index.

Section lagrange.

Variable gT : finGroupType.
Variables G H : {group gT}.
Hypotheses (HG : H \subset G).

Lemma G1 : 1%G \subset G.
Proof.
apply/subsetP => x.
by rewrite inE => /eqP ->.
Qed.

Lemma H3 g : g *: (1%G : {group gT}) = [set g].
Proof.
apply/setP => j.
rewrite !inE.
apply/idP/idP => //.
  case/lcosetP => x.
  rewrite !inE => /eqP ->.
  by rewrite mulg1 => /eqP.
move/eqP => ->.
apply/lcosetP.
 exists 1 => //.
by rewrite mulg1.
Qed.

Lemma H2 (K : {group gT}) : lcosets 1%G K = (set1) @: K.
Proof.
apply/setP => i.
apply/idP/idP.
  case/lcosetsP => g gK ->{i}.
  apply/imsetP.
  exists g => //.
  by apply H3.
case/imsetP => g gK ->{i}.
apply/lcosetsP.
exists g => //.
by rewrite H3.
Qed.

Theorem Lagrange : #| G | = (#| H | * #| lcosets H G|)%nat.
Proof. 
have [H1|H1] := boolP (1%G \proper H); last first.
  have {H1}H1 : H = 1%G.
    apply/trivGP.
    rewrite proper1G negbK in H1.
    by rewrite (eqP H1).
  rewrite H1 cards1 mul1n H2 // card_imset //.
  exact: set1_inj.
move: (index _ G H 1%G HG G1 H1).
rewrite H2.
rewrite card_imset; last first.
  exact: set1_inj.
move=> ->.
rewrite mulnC H2 card_imset //.
  exact: set1_inj.
Qed.

End lagrange.
