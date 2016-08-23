(* mathematica code for "Evolutionarily stable conjectures and ohter-regarding preferences in duopoly games" *)

SetAttributes[{ri,rj,a,b,c,t},Constant];
$Assumptions=t<1&&t>-1&&b<1&&b>0&&c>=0&&a>0&&Reals;

(* the bertrand payoff function *)
f[ii_,jj_]=ii (a*(1-b)-ii+b*jj)/(1-b^2)-c/2*((a*(1-b)-ii+b*jj)/(1-b^2))^2;

(* the utility function *)
u[m_,y_,t_]=m+t*y;

(* the possajennikov condition *)
F[xi_,xj_,ri_,ti_]=D[u[f[xi,xj],f[xj,xi],ti],xi]+ri*D[u[f[xi,xj],f[xj,xi],ti],xj];

(* the reaction function *)
reacti=Solve[F[xi,xj,ri,t]==0,xi][[1,1,2]]//FullSimplify

(* the equilibrium quantities with arbitrary conjectures *)
xsol=Solve[{F[xi,xj,ri,t]==0,F[xj,xi,rj,t]==0},{xi,xj}][[1]]//FullSimplify

(* the consistent conjecture *)
claim2=-D[F[xj,xi,rj,t],xi]/D[F[xj,xi,rj,t],xj];
rsol=Solve[rj==claim2,rj] [[2,1,2]]//FullSimplify

(* the evolutionarily stable conjeture rE *)
essfoc=D[f[xi,xj]/.xsol,ri]/.{ri->rE,rj->rE};
essconjectures=Refine[Solve[essfoc==0,rE]]//FullSimplify

(* Proposition 4 Proof Step 2: the non-asymptotic conjecture rE1 *)

(* this is the fitness when the other player has rE1 *)
arbfitness=f[xi,xj]/.xsol/.{ri->r,rj->essconjectures[[2,1,2]]};

Pr=Numerator[Together[arbfitness]];
Qr=Denominator[Together[arbfitness]];

(* Proposition 4 Proof Step 2: first compute the asymptotic conjecture rE2 *)
rE2=Solve[CoefficientList[Numerator[FullSimplify[essfoc/.rE->r]],r][[2]]*r+CoefficientList[Numerator[FullSimplify[essfoc/.rE->r]],r][[1]]==0,r][[1,1,2]]//FullSimplify

(* this is the fitness when the other player has rE2 *)
arbfitnessa=f[xi,xj]/.xsol/.{ri->r,rj->rE2};
Pra=Numerator[Together[arbfitness]];
Qra=Denominator[Together[arbfitness]];

(* for the non-asymptotic conjecture rE1 *)
Pr/.Sqrt[-(-1+b^2)^4 (-1+t)^3 (1+t)^2 (-4 b^2 (1+t)^3+(2+c)^2 (1+t (3+4 t)))]->A//Simplify
Qr/.Sqrt[-(-1+b^2)^4 (-1+t)^3 (1+t)^2 (-4 b^2 (1+t)^3+(2+c)^2 (1+t (3+4 t)))]->A//Simplify

(* these are second degree polynomials in r *)
Exponent[Pr,r]
Exponent[Qr,r]

(* the asymptotic conjecture rE2 *)
Pra//Simplify
Qra//Simplify

(* these are second degree polynomials in r *)
Exponent[Pra,r]
Exponent[Qra,r]