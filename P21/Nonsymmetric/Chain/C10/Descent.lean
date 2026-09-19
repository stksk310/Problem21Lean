import P21.Nonsymmetric.Chain.C10.TerminalFit
import P21.Nonsymmetric.Chain.C10.ColorExchange

namespace P21.Nonsymmetric
namespace EuclideanState

theorem closure_by_measure (n : ℕ) :
    ∀ {g : Generators} (s : g.Setting) (F : ℤ) (D : HerzogCriticalData g)
      (X : EuclideanState s F D), X.measureNat = n → F ∈ g.Gamma := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro g s F D X hmeasure
      by_cases hterminal : X.Terminal
      · exact X.terminal_f_mem hterminal
      · have hlt : (X.step hterminal).measureNat < n := by
          rw [← hmeasure]
          exact X.step_measureNat_lt hterminal
        have hrec := ih (X.step hterminal).measureNat hlt
          (relabelSetting s reversePerm) F (reverseHerzog D) (X.step hterminal) rfl
        simpa using hrec

theorem f_mem {g : Generators} {s : g.Setting} {F : ℤ} {D : HerzogCriticalData g}
    (X : EuclideanState s F D) : F ∈ g.Gamma := by
  exact closure_by_measure X.measureNat s F D X rfl

end EuclideanState
end P21.Nonsymmetric
