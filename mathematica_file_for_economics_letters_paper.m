(* 10.1016/j.econlet.2016.03.004 *)

(* payoffs *)
f[ii_, jj_, k_, m_] := ii (k*jj + m - ii);

(* utility functions *)
u[m_, y_, t_] := m + t*y;

(* the RHSs of the first-order conditions *)
F[xi_, xj_, r_, t_] := D[u[f[xi, xj, k, m], f[xj, xi, k, m], t], xi] + r*D[u[f[xi, xj, k, m], f[xj, xi, k, m], t], xj];

(* eq strategies *)
xsol[k_, m_, ri_, rj_, ti_, tj_] = Solve[{F[xi, xj, ri, ti] == 0, F[xj, xi, rj, tj] == 0}, {xi, xj}][[1, 1, 2]];

(* this is the equilibrium strategy for arbitrary common t *)
xsol[k, m, ri, rj, t, t] // FullSimplify

(* the eq strategy has a nonzero denominator, thus it exists for all t *)
Reduce[{4 - 4 ri rj t^2 + k^2 (-1 + ri rj) (1 + t)^2 + 2 k (ri + rj) (-1 + t^2) < 0, t < 1, t > -1, ri <= 1, ri >= -1, rj <= 1, rj >= -1, k < 1, k > -1, k != 0}]

(* Possajennikov 2000 eq 6 says this (the evol. stable ORP with zero conjectures and infinite population) *)
Solve[D[f[xsol[k, m, 0, 0, t, talt], xsol[k, m, 0, 0, talt, t], k, m], t] == 0 /. {talt -> t}, t]

(* this is the consistent conjecture *)
rsol = FullSimplify[Solve[-D[F[xj, xi, rj, t], xi]/D[F[xj, xi, rj, t], xj] == rj, rj][[1, 1, 2]], t < 1 && t > -1]

(* If players have consistent conjectures and the ORPs evolve according to the large pop ESS of Neill (2004) *)
fitnesscons = 
 f[xsol[k, m, rsol, rsol, t, talt], xsol[k, m, rsol, rsol, talt, t], k, m]*(NN - M2)/(NN - 1) + 
 f[xsol[k, m, rsol, rsol, t, t], xsol[k, m, rsol, rsol, t, t], k, m]*(M2 - 1)/(NN - 1) - 
 f[xsol[k, m, rsol, rsol, talt, t], xsol[k, m, rsol, rsol, t, talt], k, m]*M2/(NN - 1);
foccons = D[fitnesscons, t];
Solve[foccons == 0 /. talt -> t, t] // FullSimplify

(* If players have zero conjectures and the ORPs evolve according to the large pop ESS of Neill (2004) *)
fitnesszero =
 f[xsol[k, m, 0, 0, t, taltt], xsol[k, m, 0, 0, taltt, t], k, m]*(NN - M2)/(NN - 1) + 
 f[xsol[k, m, 0, 0, t, t], xsol[k, m, 0, 0, t, t], k, m]*(M2 - 1)/(NN - 1) - 
 f[xsol[k, m, 0, 0, taltt, t], xsol[k, m, 0, 0, t, taltt], k, m]*M2/(NN - 1);
foczero = D[fitnesszero, t];
Solve[foczero == 0 /. taltt -> t, t] // FullSimplify
