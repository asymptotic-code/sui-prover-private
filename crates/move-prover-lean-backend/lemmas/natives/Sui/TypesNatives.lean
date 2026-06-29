-- Native implementations for sui::types
-- Type introspection operations

import Prelude.BoundedNat
import Prelude.Helpers

namespace TypesNatives

-- Stub: actual OTW detection requires runtime type info. Returning false is
-- the safe under-approximation (treat every value as not-an-OTW); callers
-- that depend on the OTW check failing will exhibit the documented failure
-- path, which is exactly the test we want to exercise.
def is_one_time_witness (_tv0 : Type) [BEq _tv0] [Inhabited _tv0] (_param0 : _tv0) : Bool := false

end TypesNatives
