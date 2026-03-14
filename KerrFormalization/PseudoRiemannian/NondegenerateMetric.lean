import KerrFormalization.PseudoRiemannian.BilinearMetric

namespace KerrFormalization
namespace PseudoRiemannian

def IsNondegenerateMetric (g : BilinearMetric) : Prop :=
  BilinearMetric.IsNondegenerate g

end PseudoRiemannian
end KerrFormalization
