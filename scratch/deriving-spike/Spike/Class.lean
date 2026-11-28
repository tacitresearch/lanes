module

/-! A runtime class, `Init` only, as `Lanes.ToJson` is. -/

@[expose] public section

namespace Spike

/-- Names the fields of a structure. -/
class Describe (α : Type) where
  fields : List String

end Spike
