/-
  SwarmGate.Basic — payload values, payload types and refinements (THEORY.md §2).

  Payloads are JSON-like values. Types are *closed*: a record value must have exactly the declared fields,
  so a compromised agent cannot smuggle extra fields past the gate. Integers are 64-bit bounded so that
  the information capacity of every finite type is a sound upper bound (used by the IFC analysis).
-/
namespace SwarmGate

/-- JSON-like payload values. Enum constants are represented as strings. -/
inductive Value where
  | unit
  | bool (b : Bool)
  | int (i : Int)
  | str (s : String)
  | list (vs : List Value)
  | record (fs : List (String × Value))
  deriving Repr, Inhabited, BEq

mutual
/-- Payload types. Record fields are a separate mutual inductive so that `DecidableEq` can be derived. -/
inductive Ty where
  | unit
  | bool
  | int
  | str
  | enum (cases : List String)
  | list (t : Ty)
  | record (fields : Fields)
/-- Closed record field declarations. -/
inductive Fields where
  | nil
  | cons (name : String) (t : Ty) (rest : Fields)
end

deriving instance DecidableEq for Ty
deriving instance Repr for Ty
deriving instance Inhabited for Ty

def Fields.names : Fields → List String
  | .nil => []
  | .cons n _ r => n :: r.names

def Fields.length : Fields → Nat
  | .nil => 0
  | .cons _ _ r => r.length + 1

def int64Min : Int := -(2 ^ 63)
def int64Max : Int := 2 ^ 63 - 1

mutual
/-- Decidable typing judgement `v ⊨ t`. Records are closed and field order is irrelevant. -/
def hasTy : Ty → Value → Bool
  | .unit, .unit => true
  | .bool, .bool _ => true
  | .int, .int i => decide (int64Min ≤ i) && decide (i ≤ int64Max)
  | .str, .str _ => true
  | .enum cs, .str s => cs.contains s
  | .list t, .list vs => vs.all (fun v => hasTy t v)
  | .record fs, .record vs =>
      vs.length == fs.length &&
      vs.all (fun p => fs.names.contains p.1) &&
      hasFields fs vs
  | _, _ => false
termination_by structural t => t
/-- Every declared field is present (first occurrence) with the right type. -/
def hasFields : Fields → List (String × Value) → Bool
  | .nil, _ => true
  | .cons n t r, vs =>
      (match vs.find? (fun p => p.1 == n) with
       | some p => hasTy t p.2
       | none => false) && hasFields r vs
termination_by structural fs => fs
end

mutual
/-- Upper bound on the information (in bits) a value of this type can carry; `none` = unbounded. -/
def Ty.capBits : Ty → Option Nat
  | .unit => some 0
  | .bool => some 1
  | .int => some 64
  | .str => none
  | .enum cs => some (Nat.log2 (cs.length - 1) + 1)
  | .list _ => none
  | .record fs => Fields.capBits fs
def Fields.capBits : Fields → Option Nat
  | .nil => some 0
  | .cons _ t r =>
      match Ty.capBits t, Fields.capBits r with
      | some a, some b => some (a + b)
      | _, _ => none
end

/-- A message is *low-capacity* (cannot carry free-form instructions) if its type carries ≤ `maxBits`. -/
def Ty.lowcap (maxBits : Nat) (t : Ty) : Bool :=
  match t.capBits with
  | some b => decide (b ≤ maxBits)
  | none => false

/-- Field access along a path. -/
def Value.get : Value → List String → Option Value
  | v, [] => some v
  | .record fs, k :: ks =>
      match fs.find? (fun p => p.1 == k) with
      | some p => p.2.get ks
      | none => none
  | _, _ :: _ => none

/-- `needle` is a prefix of `s` (structural, so the kernel can evaluate it). -/
def isPrefixL : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a == b && isPrefixL as bs

/-- Substring test on character lists (the empty needle is contained in every string). -/
def containsL (needle : List Char) : List Char → Bool
  | [] => needle.isEmpty
  | h :: t => isPrefixL needle (h :: t) || containsL needle t

/-- Decidable payload refinements (THEORY.md §2). -/
inductive Pred where
  | tt
  | ff
  | and (p q : Pred)
  | or (p q : Pred)
  | not (p : Pred)
  | intLe (path : List String) (k : Int)
  | intGe (path : List String) (k : Int)
  | lenLe (path : List String) (k : Nat)
  | strIn (path : List String) (cs : List String)
  | strNotContains (path : List String) (needle : String)
  | eqStr (path : List String) (s : String)
  | eqBool (path : List String) (b : Bool)
  deriving Repr, Inhabited, DecidableEq

def Pred.eval : Pred → Value → Bool
  | .tt, _ => true
  | .ff, _ => false
  | .and p q, v => p.eval v && q.eval v
  | .or p q, v => p.eval v || q.eval v
  | .not p, v => !p.eval v
  | .intLe path k, v => match v.get path with | some (.int i) => decide (i ≤ k) | _ => false
  | .intGe path k, v => match v.get path with | some (.int i) => decide (k ≤ i) | _ => false
  | .lenLe path k, v => match v.get path with
      | some (.str s) => decide (s.length ≤ k)
      | some (.list vs) => decide (vs.length ≤ k)
      | _ => false
  | .strIn path cs, v => match v.get path with | some (.str s) => cs.contains s | _ => false
  | .strNotContains path n, v => match v.get path with
      | some (.str s) => !containsL n.toList s.toList
      | _ => false
  | .eqStr path s, v => match v.get path with | some (.str s') => s' == s | _ => false
  | .eqBool path b, v => match v.get path with | some (.bool b') => b' == b | _ => false

end SwarmGate
