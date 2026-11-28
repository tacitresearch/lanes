/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Net.Handshake
public import Lanes.Proof.ByteArray
public import Lanes.Data.Codec

/-!
What the handshake promises, for every key, hello and sequence of events. A hello is read back
as written, whatever follows it (`Hello.read_write_append`). A side is connected only once it
has read a hello that agrees with its own, followed by the HMAC under its key of the other
role's label and of both hellos, its own included (`Reachable.ready_proved`). Its own hello
holds the nonce it made for the connection, so bytes recorded on another connection carry the
proof of another transcript.
-/

@[expose] public section

namespace Lanes.Peers.Handshake

/-- The states `step` reaches from `start`. -/
inductive Reachable (s : Setup) : State → Prop where
  | start : Reachable s (start s).1
  | step {st : State} (e : Event) : Reachable s st → Reachable s (step s st e).1

theorem size_magic : magic.size = 8 := rfl

theorem Hello.write_eq (h : Hello) : h.write = magic ++ Frame.encode h.records := rfl

theorem Hello.size_write (h : Hello) :
    h.write.size = magic.size + Frame.span h.records := by
  rw [write_eq, ByteArray.size_append, Frame.size_encode]

/-- A hello of this version, each record of which fits a frame, reads back as written, and takes
the bytes it was written in, whatever follows. -/
theorem Hello.read_write_append (h : Hello) (rest : ByteArray) (hv : h.version = Handshake.version)
    (hfit : ∀ p ∈ h.records, p.size < 2 ^ 32) :
    read (h.write ++ rest) = .hello h h.write.size := by
  have hsize : ¬ (h.write ++ rest).size < magic.size := by
    rw [ByteArray.size_append, size_write]; omega
  have hhead : (h.write ++ rest).extract 0 magic.size = magic := by
    rw [write_eq, ByteArray.append_assoc]
    exact ByteArray.extract_append_eq_left rfl
  have hbody : (h.write ++ rest).extract magic.size (h.write ++ rest).size
      = Frame.encode h.records ++ rest := by
    rw [write_eq, ByteArray.append_assoc]
    exact ByteArray.extract_append_eq_right rfl ByteArray.size_append
  have hframes : Frame.decode (Frame.encode h.records ++ rest)
      = h.records ++ Frame.decode rest := Frame.decode_encode_append rest hfit
  unfold read
  simp only [hsize, ↓reduceIte, hhead, ne_eq, not_true_eq_false, hbody, hframes]
  have hutf8 : ∀ s : String, String.fromUTF8? s.toByteArray = some s := Codec.fromUTF8?_toUTF8
  obtain ⟨version, system, digest, nonce⟩ := h
  subst hv
  simp [records, hutf8, size_write]

/-- Two hellos agree when their versions, systems and digests are the same. -/
theorem differs_eq_none {ours theirs : Hello} :
    differs ours theirs = none ↔ ours.version = theirs.version ∧ ours.system = theirs.system
      ∧ ours.digest = theirs.digest := by
  unfold differs
  by_cases hv : ours.version = theirs.version <;> by_cases hs : ours.system = theirs.system
    <;> by_cases hd : ours.digest = theirs.digest <;> simp [hv, hs, hd]

/-- A hello that does not agree is refused, with what differs, and nothing is written. -/
theorem hear_differs {s : Setup} {received : ByteArray} {theirs : Hello} {taken : Nat}
    {why : Refusal} (hread : Hello.read received = .hello theirs taken)
    (htaken : taken ≤ s.maxHelloBytes) (hdiffers : differs s.ours theirs = some why) :
    hear s received = (.refused, [.refuse why]) := by
  simp [hear, hread, Nat.not_lt.mpr htaken, hdiffers, refuse]

/-- What a state waiting for a proof remembers of the hello it read: that it was read from what
arrived, that `heard` is the bytes it took, and that it agrees with this side's. -/
def Heard (s : Setup) : State → Prop
  | .proof theirs heard _ => ∃ received taken, Hello.read received = .hello theirs taken
      ∧ heard = received.extract 0 taken ∧ differs s.ours theirs = none
  | _ => True

theorem check_proof {s : Setup} {theirs theirs' : Hello}
    {heard heard' received received' : ByteArray}
    (h : (check s theirs heard received).1 = .proof theirs' heard' received') :
    theirs' = theirs ∧ heard' = heard := by
  unfold check refuse at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · split at h <;> cases h

theorem check_ready {s : Setup} {theirs : Hello} {heard received rest : ByteArray}
    (h : .ready rest ∈ (check s theirs heard received).2) :
    proofSize ≤ received.size
      ∧ received.extract 0 proofSize = proofOf s.key s.role.other (transcript s heard)
      ∧ rest = received.extract proofSize received.size := by
  unfold check refuse at h
  split at h
  · simp at h
  · rename_i hsize
    split at h
    · rename_i hsame
      simp only [List.mem_singleton, Action.ready.injEq] at h
      exact ⟨Nat.le_of_not_lt hsize, (Bytes.same_iff _ _).mp hsame, h⟩
    · simp at h

theorem hear_heard {s : Setup} {received : ByteArray} : Heard s (hear s received).1 := by
  unfold hear refuse
  split
  · split <;> trivial
  · trivial
  · trivial
  · trivial
  · rename_i theirs taken hread
    split
    · trivial
    · split
      · trivial
      · rename_i hdiffers
        dsimp only
        generalize hc : check s theirs (received.extract 0 taken)
          (received.extract taken received.size) = c
        obtain ⟨st, actions⟩ := c
        dsimp only
        cases st with
        | proof theirs' heard' r =>
          obtain ⟨rfl, rfl⟩ := check_proof (congrArg Prod.fst hc)
          exact ⟨received, taken, hread, rfl, hdiffers⟩
        | _ => trivial

theorem Reachable.heard {s : Setup} {st : State} (h : Reachable s st) : Heard s st := by
  induction h with
  | start => trivial
  | @step st e _ ih =>
    cases st with
    | hello received => cases e <;> first | exact hear_heard | trivial
    | proof theirs heard received =>
      cases e with
      | received bytes =>
        show Heard s (check s theirs heard (received ++ bytes)).1
        generalize hc : check s theirs heard (received ++ bytes) = c
        obtain ⟨st, actions⟩ := c
        cases st with
        | proof theirs' heard' r =>
          obtain ⟨rfl, rfl⟩ := check_proof (congrArg Prod.fst hc)
          exact ih
        | _ => trivial
      | _ => trivial
    | _ => cases e <;> trivial

theorem hear_ready {s : Setup} {received rest : ByteArray}
    (h : .ready rest ∈ (hear s received).2) :
    ∃ theirs taken, Hello.read received = .hello theirs taken ∧ differs s.ours theirs = none
      ∧ ∃ proof : ByteArray, proofSize ≤ proof.size
        ∧ proof.extract 0 proofSize
          = proofOf s.key s.role.other (transcript s (received.extract 0 taken))
        ∧ rest = proof.extract proofSize proof.size := by
  unfold hear refuse at h
  split at h
  · split at h <;> simp at h
  · simp at h
  · simp at h
  · simp at h
  · rename_i theirs taken hread
    split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i hdiffers
        simp only [List.mem_cons, reduceCtorEq, false_or] at h
        exact ⟨theirs, taken, hread, hdiffers, _, check_ready h⟩

/-- A side is connected only once it has read a hello that agrees with its own, then the proof
of the other role: the HMAC under this side's key of both hellos, this side's own, with the
nonce it made for the connection, included. -/
theorem Reachable.ready_proved {s : Setup} {st : State} {e : Event} {rest : ByteArray}
    (h : Reachable s st) (hready : Action.ready rest ∈ (Handshake.step s st e).2) :
    ∃ theirs received taken, Hello.read received = .hello theirs taken
      ∧ differs s.ours theirs = none
      ∧ ∃ proof : ByteArray, proofSize ≤ proof.size
        ∧ proof.extract 0 proofSize
          = proofOf s.key s.role.other (transcript s (received.extract 0 taken))
        ∧ rest = proof.extract proofSize proof.size := by
  have hheard := h.heard
  cases st <;> cases e <;> simp only [Handshake.step, refuse, List.mem_singleton, List.not_mem_nil,
    reduceCtorEq] at hready
  · obtain ⟨theirs, taken, hread, hdiffers, proof⟩ := hear_ready hready
    exact ⟨theirs, _, taken, hread, hdiffers, proof⟩
  · rename_i theirs heard received bytes
    obtain ⟨received₀, taken, hread, rfl, hdiffers⟩ := hheard
    exact ⟨theirs, received₀, taken, hread, hdiffers, _, check_ready hready⟩

end Lanes.Peers.Handshake
