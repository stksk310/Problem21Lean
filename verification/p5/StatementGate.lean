import P21.Nonsymmetric.Path.Packets

#check P21.Nonsymmetric.PathInput.beta
#check P21.Nonsymmetric.PathInput.alpha
#check P21.Nonsymmetric.PathInput.P0
#check P21.Nonsymmetric.PathInput.T
#check P21.Nonsymmetric.PathInput.beta_pos
#check P21.Nonsymmetric.PathInput.alpha_pos
#check P21.Nonsymmetric.PathInput.P0_eq
#check P21.Nonsymmetric.PathInput.T_eq
#check P21.Nonsymmetric.PathInput.R_pos
#check P21.Nonsymmetric.PathInput.R_lt
#check P21.Nonsymmetric.PathInput.qL_eq
#check P21.Nonsymmetric.PathInput.qA_eq
#check P21.Nonsymmetric.PathInput.qB_eq
#check P21.Nonsymmetric.PathInput.qR_eq

-- P5.1 actual-return gate: each witness retains its original full
-- nonnegative factorization and records the missing tail coordinate.
#check P21.Nonsymmetric.PathInput.ActualReturn
#check P21.Nonsymmetric.PathInput.qL_n1_return
#check P21.Nonsymmetric.PathInput.qL_n2_return
#check P21.Nonsymmetric.PathInput.qR_n0_return
#check P21.Nonsymmetric.PathInput.qR_n1_return

-- P5.2 full PATH left-right transport (0 <-> 2, 1 fixed).
#check P21.Nonsymmetric.pathReversePerm
#check P21.Nonsymmetric.pathReverseHerzog
#check P21.Nonsymmetric.pathReverseHerzog_fA
#check P21.Nonsymmetric.pathReverseHerzog_fB
#check P21.Nonsymmetric.PathInput.reverse

-- P5.1 starts from these two named actual H-factorizations.
#check P21.Nonsymmetric.PathInput.CentralReturns
#check P21.Nonsymmetric.PathInput.central_returns
#check P21.Nonsymmetric.replacePacketCopies
#check P21.Nonsymmetric.reduceCriticalCoordinate
#check P21.Nonsymmetric.reduceCriticalCoordinate_lt
