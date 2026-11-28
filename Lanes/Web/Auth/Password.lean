/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Crypto.Native
public import Lanes.Lib.Encoding.Base64
public import Lanes.Lib.Encoding.Digits
public import Lanes.Data.Declare

/-!
Password hashes, in two forms.

A stored hash (`Stored`) is a PHC string, `$argon2id$v=19$m=<KiB>,t=<passes>,p=<lanes>$<salt>$<hash>`
with the salt and the hash in base64 without padding, as libsodium's `crypto_pwhash_str` and
Argon2's reference implementation write it (`Phc`). It carries what made it, so
`Password.verify` reads the cost and the salt from it: raising the cost or changing the pepper
leaves it readable, and `Verdict.rehash` says when to store it again at the deployment's cost.
A new hash has a salt of 16 random bytes (`Password.hash`). Verifying needs the stored hash, so
it is done where both it and the password are, off the shard: an adapter's handler, or a
request's own task.

A digest (`Digest`, `Password.digest`) is the raw 32 bytes of Argon2id under a salt derived from
the user's name and a secret of the deployment, for a system that is given the digest of a
log-in before it has seen the request, and so before it could give a random salt. It is
compared as it is, and changes with the cost and the pepper. A stored digest of this form reads
as `Stored.raw`, and verifies only under the cost and pepper that made it, as `rehash`.
-/

@[expose] public section

namespace Lanes.Auth

/-- A password digest. Two are compared in time that does not depend on where they differ, so
`if d = stored` in a step function does not leak the stored digest byte by byte. -/
structure Digest where
  bytes : ByteArray

instance : DecidableEq Digest := fun a b =>
  if h : Bytes.same a.bytes b.bytes then
    isTrue (by cases a; cases b; exact congrArg _ ((Bytes.same_iff _ _).mp h))
  else isFalse (by intro heq; exact h ((Bytes.same_iff _ _).mpr (heq ▸ rfl)))

instance : Hashable Digest := ⟨fun d => hash d.bytes⟩

instance : Repr Digest := ⟨fun d _ => s!"<digest {(Bytes.hex d.bytes).take 8}>"⟩

/-- A digest as text, so that a request prepared where it arrives can carry it into the bridge
in place of the password. -/
def Digest.hex (d : Digest) : String := Bytes.hex d.bytes

def Digest.ofHex? (s : String) : Option Digest := (Bytes.unhex? s).map (⟨·⟩)

theorem Digest.ofHex?_hex (d : Digest) : ofHex? d.hex = some d := by
  simp [ofHex?, hex, Bytes.unhex?_hex]

/-- An Argon2id hash, version 19, with what made it: the salt is 8 to 64 bytes. Lanes computes
hashes of 32 bytes, so one of another length never verifies. -/
structure Phc where
  cost : Argon2id
  lanes : UInt32
  salt : ByteArray
  hash : ByteArray
  lanes_ok : 0 < lanes.toNat ∧ lanes.toNat < 2 ^ 24 ∧ 8 * lanes.toNat ≤ cost.mem_kib.toNat
  salt_ok : 8 ≤ salt.size ∧ salt.size ≤ 64

namespace Phc

/-- The text before the first `c`, and the text after it. -/
def cut (c : Char) : List Char → Option (List Char × List Char)
  | [] => none
  | d :: rest => if d = c then some ([], rest) else (cut c rest).map fun (a, b) => (d :: a, b)

/-- What follows `p`, if the text starts with it. -/
def after : List Char → List Char → Option (List Char)
  | [], cs => some cs
  | p :: ps, c :: cs => if p = c then after ps cs else none
  | _ :: _, [] => none

/-- A field of at most ten digits, as a 32-bit number. -/
def number? (cs : List Char) : Option UInt32 :=
  if cs.length ≤ 10 then
    (Digits.ofChars? 10 cs).bind fun n => if n < 2 ^ 32 then some n.toUInt32 else none
  else none

def encode (p : Phc) : String :=
  String.ofList ("$argon2id$v=19$m=".toList ++ Digits.toChars 10 p.cost.mem_kib.toNat
    ++ ',' :: 't' :: '=' :: Digits.toChars 10 p.cost.ops.toNat
    ++ ',' :: 'p' :: '=' :: Digits.toChars 10 p.lanes.toNat
    ++ '$' :: Base64.encodeList .rawStd p.salt.data.toList
    ++ '$' :: Base64.encodeList .rawStd p.hash.data.toList)

/-- A PHC string of Argon2id, version 19, its parameters in the order `m`, `t`, `p`. -/
def parse? (s : String) : Option Phc := do
  let rest ← after "$argon2id$v=19$m=".toList s.toList
  let (m, rest) ← cut ',' rest
  let rest ← after "t=".toList rest
  let (t, rest) ← cut ',' rest
  let rest ← after "p=".toList rest
  let (p, rest) ← cut '$' rest
  let (salt, hash) ← cut '$' rest
  let mem_kib ← number? m
  let ops ← number? t
  let lanes ← number? p
  let salt ← (Base64.decodeList .rawStd salt).map (ByteArray.mk ·.toArray)
  let hash ← (Base64.decodeList .rawStd hash).map (ByteArray.mk ·.toArray)
  if h : 0 < ops ∧ 8 ≤ mem_kib then
    let cost : Argon2id := ⟨ops, mem_kib, h.1, h.2⟩
    if h' : (0 < lanes.toNat ∧ lanes.toNat < 2 ^ 24 ∧ 8 * lanes.toNat ≤ cost.mem_kib.toNat)
        ∧ (8 ≤ salt.size ∧ salt.size ≤ 64) then
      some ⟨cost, lanes, salt, hash, h'.1, h'.2⟩
    else none
  else none

/-- Whether `password` gives this hash under its cost, lanes and salt, compared in time that
does not depend on where they differ. -/
def check (p : Phc) (password : ByteArray) : Bool :=
  Bytes.same (p.cost.derive p.lanes password p.salt .empty .empty p.salt_ok.1 p.lanes_ok) p.hash

theorem check_iff (p : Phc) (password : ByteArray) :
    p.check password = true
      ↔ p.cost.derive p.lanes password p.salt .empty .empty p.salt_ok.1 p.lanes_ok = p.hash :=
  Bytes.same_iff _ _

instance : DecidableEq Phc := fun a b =>
  if h : a.cost.ops = b.cost.ops ∧ a.cost.mem_kib = b.cost.mem_kib ∧ a.lanes = b.lanes
      ∧ a.salt = b.salt ∧ Bytes.same a.hash b.hash then
    isTrue (by
      obtain ⟨⟨ao, am, _, _⟩, al, as, ah, _, _⟩ := a
      obtain ⟨⟨bo, bm, _, _⟩, bl, bs, bh, _, _⟩ := b
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      simp only at h1 h2 h3 h4 h5
      subst h1 h2 h3 h4
      cases (Bytes.same_iff _ _).mp h5
      rfl)
  else isFalse (by
    intro heq
    subst heq
    exact h ⟨rfl, rfl, rfl, rfl, (Bytes.same_iff _ _).mpr rfl⟩)

instance : Repr Phc := ⟨fun p _ => s!"<argon2id m={p.cost.mem_kib},t={p.cost.ops},p={p.lanes}>"⟩

/-! The string reads back as the hash it was written from. -/

theorem cut_append {c : Char} {a b : List Char} (h : c ∉ a) : cut c (a ++ c :: b) = some (a, b) := by
  induction a with
  | nil => simp [cut]
  | cons d a ih =>
    have hd : d ≠ c := fun e => h (e ▸ List.mem_cons_self ..)
    simp [cut, hd, ih (fun m => h (List.mem_cons_of_mem _ m))]

theorem after_append (p r : List Char) : after p (p ++ r) = some r := by
  induction p with
  | nil => rfl
  | cons c p ih => simp [after, ih]

theorem not_mem_toChars {c : Char} (hc : c ∉ Digits.lower) (n : Nat) : c ∉ Digits.toChars 10 n :=
  fun h => hc (Digits.mem_toChars (by omega) (by omega) h)

theorem number?_toChars (n : UInt32) : number? (Digits.toChars 10 n.toNat) = some n := by
  have hlt := n.toNat_lt
  have hlen := Digits.length_toChars_le (b := 10) (k := 10) (by omega) (by omega)
    (Nat.lt_trans hlt (by decide))
  simp [number?, hlen, Digits.ofChars?_toChars (b := 10) (by omega) (by omega), hlt]

theorem mem_encodeList {e : Base64.Encoding} {c : Char} :
    ∀ {bytes : List UInt8}, c ∈ Base64.encodeList e bytes → c = '=' ∨ ∃ v, c = e.alphabet.char v
  | [], h => by simp [Base64.encodeList] at h
  | [_], h | [_, _], h => by
    simp only [Base64.encodeList, Base64.pad, List.cons_append, List.nil_append,
      List.mem_cons] at h
    split at h <;> simp only [List.mem_replicate, List.not_mem_nil] at h <;>
      rcases h with rfl | rfl | h <;> first | exact .inr ⟨_, rfl⟩ | skip
    all_goals first
      | (rcases h with rfl | h <;> first | exact .inr ⟨_, rfl⟩ | skip)
      | skip
    all_goals simp_all
  | _ :: _ :: _ :: rest, h => by
    simp only [Base64.encodeList, List.mem_cons] at h
    rcases h with rfl | rfl | rfl | rfl | h
    any_goals exact .inr ⟨_, rfl⟩
    exact mem_encodeList h

theorem dollar_not_mem_encodeList (bytes : List UInt8) : '$' ∉ Base64.encodeList .rawStd bytes := by
  intro h
  rcases mem_encodeList h with h | ⟨v, hv⟩
  · cases h
  · revert hv; revert v; decide

theorem parse?_encode (p : Phc) : parse? p.encode = some p := by
  obtain ⟨⟨ops, mem_kib, hops, hmem⟩, lanes, salt, hash, hl, hs⟩ := p
  have hd : ∀ n, ',' ∉ Digits.toChars 10 n := not_mem_toChars (by decide)
  have hd' : ∀ n, '$' ∉ Digits.toChars 10 n := not_mem_toChars (by decide)
  simp only [parse?, encode, String.toList_ofList, List.append_assoc, List.cons_append,
    after_append, show "t=".toList = ['t', '='] from rfl, show "p=".toList = ['p', '='] from rfl,
    after, ite_true, cut_append (hd _), cut_append (hd' _), cut_append (dollar_not_mem_encodeList _),
    Option.bind_eq_bind, Option.bind_some, number?_toChars, Base64.decodeList_encodeList,
    Option.map_some, Array.toArray_toList]
  simp [hops, hmem, hl, hs]

end Phc

/-- What is stored of a password: a PHC string, or a digest Lanes stored before it wrote them. -/
inductive Stored where
  | phc (p : Phc)
  | raw (d : Digest)
  deriving DecidableEq, Repr

namespace Stored

/-- A PHC string starts with `$`, and a digest is in hex, which never does. -/
def text : Stored → String
  | .phc p => p.encode
  | .raw d => d.hex

def read? (s : String) : Option Stored :=
  match s.toList with
  | '$' :: _ => (Phc.parse? s).map .phc
  | _ => (Digest.ofHex? s).map .raw

private theorem hexDigit_ne : ∀ b : UInt8, Bytes.hexDigit b ≠ '$' := by decide

theorem read?_text (s : Stored) : read? s.text = some s := by
  cases s with
  | phc p =>
    obtain ⟨rest, hr⟩ : ∃ rest, p.encode.toList = '$' :: rest := ⟨_, by simp [Phc.encode]; rfl⟩
    simp only [read?, text, hr, Phc.parse?_encode, Option.map_some]
  | raw d =>
    have hn : ∀ rest, d.hex.toList ≠ '$' :: rest := by
      intro rest h
      obtain ⟨⟨⟨l⟩⟩⟩ := d
      cases l with
      | nil => simp [Digest.hex, Bytes.hex] at h
      | cons b l =>
        simp [Digest.hex, Bytes.hex] at h
        exact hexDigit_ne _ h.1
    unfold read? text
    split
    · rename_i rest h; exact absurd h (hn rest)
    · simp only [Digest.ofHex?_hex, Option.map_some]

end Stored

structure Password where
  cost : Argon2id
  /-- A secret of the deployment, kept with its key; it salts digests (`Password.digest`), and
  changing it changes every digest. -/
  pepper : ByteArray

def Password.salt (config : Password) (user : String) : ByteArray :=
  (hmac config.pepper ("salt\x00" ++ user).toUTF8).extract 0 16

theorem Password.size_salt (config : Password) (user : String) : (config.salt user).size = 16 := by
  simp [Password.salt, Hmac.size_hmac]

def Password.digest (config : Password) (user password : String) : Digest :=
  ⟨config.cost.hash password.toUTF8 (config.salt user) (config.size_salt user)⟩

/-- A new hash of `password` at the deployment's cost, in one lane, under `salt`: 16 bytes from
`randomBytes`, drawn for this hash. -/
def Password.hash (config : Password) (salt : ByteArray) (h : salt.size = 16) (password : String) :
    Phc :=
  { cost := config.cost, lanes := 1, salt, hash := config.cost.hash password.toUTF8 salt h,
    lanes_ok := config.cost.oneLane, salt_ok := by omega }

/-- What a password is, checked against what is stored of it. -/
inductive Verdict where
  | wrong
  | ok
  /-- Right, but stored otherwise than the deployment would store it now: store
  `Password.hash` of it in its place. -/
  | rehash
  deriving DecidableEq, Repr

/-- Whether a hash is as the deployment makes one now: its cost, one lane, 16 bytes of salt. -/
def Password.current (config : Password) (p : Phc) : Bool :=
  p.cost.ops == config.cost.ops && p.cost.mem_kib == config.cost.mem_kib && p.lanes == 1
    && p.salt.size == 16

/-- `password` against what is stored of `user`'s. A PHC string is checked under its own cost
and salt; a digest under the deployment's, which must be the ones that made it. -/
def Password.verify (config : Password) (user : String) (password : String) : Stored → Verdict
  | .phc p => if p.check password.toUTF8 then (if config.current p then .ok else .rehash) else .wrong
  | .raw d => if config.digest user password = d then .rehash else .wrong

theorem Password.verify_hash (config : Password) (user : String) {salt : ByteArray}
    (h : salt.size = 16) (password : String) :
    config.verify user password (.phc (config.hash salt h password)) = .ok := by
  have hc : (config.hash salt h password).check password.toUTF8 = true :=
    (Phc.check_iff _ _).mpr rfl
  simp only [verify, hc, ite_true]
  simp [current, Password.hash, h]

/-- A password passes only if it gives the stored hash under the stored cost and salt. -/
theorem Password.verify_phc {config : Password} {user password : String} {p : Phc}
    (h : config.verify user password (.phc p) ≠ .wrong) :
    p.cost.derive p.lanes password.toUTF8 p.salt .empty .empty p.salt_ok.1 p.lanes_ok = p.hash := by
  simp only [verify] at h
  split at h
  · exact (Phc.check_iff _ _).mp (by assumption)
  · exact absurd rfl h

/-- A digest is never as the deployment stores a password now. -/
theorem Password.verify_raw (config : Password) (user password : String) (d : Digest) :
    config.verify user password (.raw d) ≠ .ok := by
  simp only [verify]
  split <;> simp

end Lanes.Auth
