(* mathematica code for "Evolutionarily stable conjectures and ohter-regarding preferences in duopoly games" *)

SetAttributes[{ri,rj,a,b,c,t},Constant];
$Assumptions=t<1&&t>-1&&b<1&&b>0&&c>=0&&a>0&&Reals;

(* the cournot payoff function *)
f[ii_,jj_]=ii*(a-ii-b*jj)-c*ii^2; 

(* the utility function *)
u[m_,y_,t_]=m+t*y; 

(* the possajennikov condition *)
F[xi_,xj_,ri_,ti_]=D[u[f[xi,xj],f[xj,xi],ti],xi]+ri*D[u[f[xi,xj],f[xj,xi],ti],xj]; 

(* the reaction function in the Cournot case *)
reacti=Solve[F[xi,xj,ri,t]==0,xi][[1,1,2]]//FullSimplify

(* solve the equilibrium quantities with arbitrary conjectures *)
xsol=Solve[{F[xi,xj,ri,t]==0,F[xj,xi,rj,t]==0},{xi,xj}][[1]]//FullSimplify

(* solve the consistent conjectures *)
claim2=-D[F[xj,xi,rj,t],xi]/D[F[xj,xi,rj,t],xj];
rsol=Solve[rj==claim2,rj][[2,1,2]] //FullSimplify

(* solve the evolutionarily stable conjectures rE *)
essfoc=D[f[xi,xj]/.xsol,ri]/.{ri->rE,rj->rE};
essconjectures=Solve[essfoc==0,rE] //FullSimplify
