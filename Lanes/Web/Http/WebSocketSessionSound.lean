/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Web.Http.WebSocketSession
public import Lanes.Web.Http.WebSocketSound

/-!
What a socket's side of the server (`Lanes.Web.Http.WebSocketSession`) is proved to do, for
every configuration and every event:

- every write but the answer to the head is frames a client reads back, one after another:
  unmasked, none longer than `Session.Config.cap`, every control frame whole and at most 125
  bytes (`Session.step_writes`), so that `decode` reads each back (`WebSocket.decode_encode`); a
  close's reason is cut to fit (`WebSocket.size_closePayload`);
- what `Conn.receive` sends back is such frames (`Conn.receive_sends`);
- a socket hands the system at most one request in a step, and none while one is with it, but
  for the answer to that one (`Session.step_submits`, `Session.step_withSystem`), so it holds
  at most one place among the gate's pending requests.
-/

@[expose] public section

namespace Lanes.WebSocket

/-- Bytes that are frames a server may write, back to back: unmasked, and each one a reader
whose limits on a frame and on a message are at least `cap` reads back. -/
inductive Frames (cap : Nat) : ByteArray → Prop
  | empty : Frames cap .empty
  | cons {f : Frame} {rest : ByteArray} : f.mask = none → f.Valid ⟨cap, cap⟩ → Frames cap rest →
    Frames cap (encode f ++ rest)

variable {cap : Nat}

theorem Frames.append {a b : ByteArray} (ha : Frames cap a) (hb : Frames cap b) :
    Frames cap (a ++ b) := by
  induction ha with
  | empty => simpa using hb
  | cons hm hv _ ih => rw [ByteArray.append_assoc]; exact .cons hm hv ih

theorem Frames.single {f : Frame} (hm : f.mask = none) (hv : f.Valid ⟨cap, cap⟩) :
    Frames cap (encode f) := by
  simpa using Frames.cons hm hv .empty

/-- A frame of at most 125 bytes, whole and unmasked, as every control frame the server sends. -/
theorem Frames.small (h125 : 125 ≤ cap) {op : Opcode} {payload : ByteArray}
    (hp : payload.size ≤ 125) : Frames cap (Conn.frameBytes op payload) :=
  Frames.single rfl ⟨by show payload.size ≤ min cap cap; omega,
    by show payload.size < 2 ^ 63; omega, fun _ => ⟨rfl, hp⟩⟩

theorem size_cut (b : ByteArray) : ∀ n, (cut b n).size ≤ n
  | 0 => by simp [cut]
  | n + 1 => by
    unfold cut
    split
    · simp only [ByteArray.size_extract]; omega
    · have := size_cut b n; omega

theorem size_closePayload (code : Nat) (reason : String) : (closePayload code reason).size ≤ 125 := by
  have := size_cut reason.toUTF8 123
  simp only [closePayload, ByteArray.size_append]
  have : (⟨#[(code / 256).toUInt8, (code % 256).toUInt8]⟩ : ByteArray).size = 2 := rfl
  omega

/-! ### What a connection sends back -/

/-- Every byte array `events` sends is frames. -/
def Sends (cap : Nat) (events : List Event) : Prop := ∀ b, Event.send b ∈ events → Frames cap b

theorem Sends.append {a b : List Event} (ha : Sends cap a) (hb : Sends cap b) : Sends cap (a ++ b) :=
  fun x hx => (List.mem_append.1 hx).elim (ha x) (hb x)

/-- A control frame `decode` reads holds at most 125 bytes. -/
theorem decode_control {l : Limits} {bytes : ByteArray} {masked : Option Bool} {sofar : Nat}
    {f : Frame} {n : Nat} (h : decode l bytes masked sofar = .frame f n)
    (hc : f.opcode.control = true) : f.payload.size ≤ 125 := by
  unfold decode at h
  split at h
  · cases h
  · cases h
  · rename_i hd _
    split at h
    · cases h
    · rename_i hsize
      split at h
      · cases h
      · rename_i hok
        simp only [Decoded.frame.injEq] at h
        obtain ⟨rfl, -⟩ := h
        simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true',
          not_or] at hok hc
        have hl : ¬ (hd.fin = false ∨ hd.length > 125) := fun h => hok.2 ⟨hc, h⟩
        have : (bytes.extract hd.size (hd.size + hd.length)).size ≤ hd.length := by
          simp only [ByteArray.size_extract]; omega
        split <;> simp only [size_applyMask] <;> omega

section

variable (h125 : 125 ≤ cap)
include h125

theorem Conn.fail_sends (c : Conn) (code : Nat) : Sends cap (c.fail code).2 := by
  intro b hb
  simp only [Conn.fail, List.mem_cons, Event.send.injEq, reduceCtorEq] at hb
  rcases hb with rfl | h | h
  · exact Frames.small h125 (size_closePayload code "")
  · cases h
  · cases h

theorem Conn.deliver_sends (c : Conn) (isText : Bool) (bytes : ByteArray) :
    Sends cap (c.deliver isText bytes).2 := by
  unfold Conn.deliver
  split
  · split
    · intro b hb; simp at hb
    · exact Conn.fail_sends h125 c _
  · intro b hb; simp at hb

theorem Conn.frame_sends (c : Conn) {f : Frame} (hf : f.opcode.control = true → f.payload.size ≤ 125) :
    Sends cap (c.frame f).2 := by
  have none : ∀ c' : Conn, Sends cap (Prod.snd (c', ([] : List Event))) := fun _ b hb => by simp at hb
  have data : ∀ isText payload, Sends cap
      (if c.fragments.isSome = true then c.fail protocolError
       else if f.fin = true then c.deliver isText payload
       else ({ c with fragments := some (isText, payload) }, [])).2 := by
    intro isText payload
    split
    · exact Conn.fail_sends h125 c _
    · split
      · exact Conn.deliver_sends h125 c _ _
      · exact none _
  unfold Conn.frame
  cases hop : f.opcode
  · dsimp only
    split
    · exact Conn.fail_sends h125 c _
    · split
      · exact Conn.fail_sends h125 c _
      · split
        · exact Conn.deliver_sends h125 _ _ _
        · exact none _
  · exact data _ _
  · exact data _ _
  · dsimp only
    split
    · exact Conn.fail_sends h125 c _
    · intro b hb
      dsimp only at hb
      split at hb
      · simp at hb
      · simp only [List.cons_append, List.nil_append, List.mem_cons, Event.send.injEq,
          reduceCtorEq] at hb
        rcases hb with rfl | h | h
        · exact Frames.small h125 (hf (by rw [hop]; rfl))
        · cases h
        · cases h
  · intro b hb
    dsimp only at hb
    split at hb
    · simp at hb
    · simp only [List.mem_singleton, Event.send.injEq] at hb
      subst hb
      exact Frames.small h125 (hf (by rw [hop]; rfl))
  · exact none _

theorem Conn.drain_sends : ∀ (c : Conn) (fuel : Nat) (out : List Event), Sends cap out →
    Sends cap (c.drain fuel out).2
  | c, 0, out, h => by simpa [Conn.drain] using h
  | c, fuel + 1, out, h => by
    unfold Conn.drain
    split
    · exact h
    · split
      · exact h
      · exact h.append (Conn.fail_sends h125 c _)
      · rename_i f size hd
        exact Conn.drain_sends _ fuel _
          (h.append (Conn.frame_sends h125 _ (decode_control hd)))

/-- What a connection sends back, pongs and closes, is frames. -/
theorem Conn.receive_sends (c : Conn) (bytes : ByteArray) : Sends cap (c.receive bytes).2 := by
  unfold Conn.receive
  split
  · intro b hb; simp at hb
  · exact Conn.drain_sends h125 _ _ _ (fun b hb => by simp at hb)

end

/-! ### What the session writes -/

namespace Session

theorem cap_ge (cfg : Config) : 125 ≤ cfg.cap := by
  simp only [Config.cap]; omega

theorem cap_lt (cfg : Config) : cfg.cap < 2 ^ 63 := by
  simp only [Config.cap]; omega

/-- A message as `fragments` writes it is frames, each at most `cap` bytes. -/
theorem fragments_frames {cap : Nat} (h125 : 125 ≤ cap) (hlt : cap < 2 ^ 63) (op : Opcode)
    (hop : op.control = false) (payload : ByteArray) : Frames cap (fragments cap op payload) := by
  rw [fragments]
  split
  · exact Frames.single rfl ⟨by show payload.size ≤ min cap cap; omega,
      by show payload.size < 2 ^ 63; omega, fun h => by simp_all⟩
  · have hs : (payload.extract 0 (max 1 cap)).size ≤ cap := by
      simp only [ByteArray.size_extract]; omega
    exact (Frames.single rfl ⟨by show (payload.extract 0 (max 1 cap)).size ≤ min cap cap; omega,
      by show (payload.extract 0 (max 1 cap)).size < 2 ^ 63; omega,
      fun h => by simp_all⟩).append (fragments_frames h125 hlt .continuation rfl _)
termination_by payload.size
decreasing_by simp only [ByteArray.size_extract]; omega

variable {cfg : Config} {now : Nat}

/-- What is waiting to be written is frames. -/
abbrev Inv (cfg : Config) (s : Session) : Prop := Frames cfg.cap s.outbox

theorem start_inv (head : Http.Request) (r : Http.Response) : Inv cfg (start cfg now head r) := by
  unfold start
  split <;> exact .empty

theorem close_frames (c : Conn) (code : Nat) (reason : String) :
    Frames cfg.cap (c.close code reason).2 :=
  Frames.small (cap_ge cfg) (size_closePayload code reason)

theorem closeWith_inv {s : Session} (h : Inv cfg s) (code : Nat) (reason : String) :
    Inv cfg (closeWith now code reason s) := by
  unfold closeWith
  split
  · exact h.append (close_frames _ _ _)
  · exact h

theorem failWith_inv {s : Session} (h : Inv cfg s) (code : Nat) : Inv cfg (failWith code s) := by
  unfold failWith
  split
  · exact h
  · show Frames _ (_ ++ _)
    split
    · exact h.append (close_frames _ _ _)
    · show Frames _ (_ ++ ByteArray.empty)
      simpa using h

theorem sendMessage_inv {s : Session} (h : Inv cfg s) (m : Message) :
    Inv cfg (sendMessage cfg m s) := by
  cases m <;>
  · unfold sendMessage
    split
    · exact h
    · dsimp only
      split
      · exact h.append (fragments_frames (cap_ge cfg) (cap_lt cfg) _ rfl _)
      · exact failWith_inv Frames.empty _

theorem absorb_inv : ∀ {s : Session} {events : List Event}, Inv cfg s → Sends cfg.cap events →
    Inv cfg (absorb s events)
  | _, [], h, _ => h
  | s, .message m :: rest, h, he =>
    absorb_inv (s := { s with inbox := s.inbox ++ [m] }) (events := rest) h
      fun b hb => he b (List.mem_cons_of_mem _ hb)
  | s, .send b :: rest, h, he =>
    absorb_inv (s := { s with outbox := s.outbox ++ b }) (events := rest)
      (h.append (he b List.mem_cons_self)) fun b hb => he b (List.mem_cons_of_mem _ hb)
  | s, .closed code :: rest, h, he =>
    absorb_inv (s := { s with ended := s.ended <|> some code }) (events := rest) h
      fun b hb => he b (List.mem_cons_of_mem _ hb)

theorem receive_inv {s : Session} (h : Inv cfg s) (bytes : ByteArray) :
    Inv cfg (receive now bytes s) := by
  unfold receive
  split
  · exact h
  · exact absorb_inv h (Conn.receive_sends (cap_ge cfg) _ _)

theorem answered_inv {s : Session} (h : Inv cfg s) (index : Nat) (r : Http.Response) :
    Inv cfg (answered cfg now index r s) := by
  unfold answered
  repeat' split
  all_goals first | exact h | (dsimp only; refine closeWith_inv ?_ _ _; exact h)

theorem pushed_inv {s : Session} (h : Inv cfg s) (r : Http.Response) : Inv cfg (pushed cfg now r s) := by
  unfold pushed
  split
  · exact sendMessage_inv h _
  · exact closeWith_inv h _ _
  · exact closeWith_inv h _ _

theorem tick_inv {s : Session} (h : Inv cfg s) : Inv cfg (tick cfg now s) := by
  unfold tick
  repeat' split
  all_goals first
    | exact h
    | exact failWith_inv h _
    | exact h.append (Frames.small (cap_ge cfg) (by simp))

theorem offer_outbox (s : Session) : (offer now s).1.outbox = s.outbox := by
  unfold offer
  repeat' split
  all_goals rfl

/-- `flush` writes only what is waiting, and leaves frames waiting. -/
theorem flush_writes {s : Session} (h : Inv cfg s) :
    Inv cfg (flush s).1 ∧ ∀ b, .write b ∈ (flush s).2 → Frames cfg.cap b := by
  unfold flush
  split
  · exact ⟨h, by simp⟩
  · split
    · refine ⟨.empty, fun b hb => ?_⟩
      split at hb
      · split at hb
        · simp at hb
        · simp only [List.cons_append, List.nil_append, List.mem_cons, Http.Upgrade.Action.write.injEq,
            reduceCtorEq] at hb
          rcases hb with rfl | h' | h'
          · exact h
          · cases h'
          · cases h'
      · simp at hb
    · split
      · refine ⟨.empty, fun b hb => ?_⟩
        simp only [List.mem_singleton, Http.Upgrade.Action.write.injEq] at hb
        subst hb; exact h
      · exact ⟨h, by simp⟩

theorem advance_writes {s : Session} (h : Inv cfg s) :
    Inv cfg (advance now s).1 ∧ ∀ b, .write b ∈ (advance now s).2 → Frames cfg.cap b := by
  have ho : Inv cfg (offer now s).1 := by unfold Inv; rw [offer_outbox]; exact h
  have hoff : ∀ b, Http.Upgrade.Action.write b ∉ (offer now s).2 := by
    intro b hb
    unfold offer at hb
    repeat' split at hb
    all_goals simp at hb
  obtain ⟨h1, h2⟩ := flush_writes ho
  refine ⟨h1, fun b hb => ?_⟩
  simp only [advance, List.mem_append] at hb
  rcases hb with hb | hb
  · exact absurd hb (hoff b)
  · exact h2 b hb

/-- Every write of the session but the answer to the head is frames a client reads back, and
what waits to be written stays so. -/
theorem step_writes {s : Session} (h : Inv cfg s) (e : Http.Upgrade.Event) :
    Inv cfg (step cfg now s e).1
      ∧ ∀ b, .write b ∈ (step cfg now s e).2 → b = s.hello ∨ Frames cfg.cap b := by
  have lift : ∀ {s' : Session}, Inv cfg s' → Inv cfg (advance now s').1
      ∧ ∀ b, .write b ∈ (advance now s').2 → b = s.hello ∨ Frames cfg.cap b :=
    fun h' => ⟨(advance_writes h').1, fun b hb => .inr ((advance_writes h').2 b hb)⟩
  cases e with
  | attached rest =>
    simp only [step]
    split
    · exact ⟨h, by simp⟩
    · have hr : Inv cfg (receive now rest { s with attached := true, heard_ms := now, writing := true }) :=
        receive_inv (s := { s with attached := true, heard_ms := now, writing := true }) h rest
      obtain ⟨h1, h2⟩ := advance_writes (now := now) hr
      refine ⟨h1, fun b hb => ?_⟩
      simp only [List.mem_cons, Http.Upgrade.Action.write.injEq] at hb
      rcases hb with rfl | hb
      · exact .inl rfl
      · exact .inr (h2 b hb)
  | received bytes => exact lift (receive_inv h bytes)
  | ended => exact lift h
  | broken => exact lift h
  | sent => exact lift h
  | tick => exact lift (tick_inv h)
  | stop => exact lift (closeWith_inv (s := { s with stopping := true }) h _ _)
  | answered index r => exact lift (answered_inv h index r)
  | pushed r => exact lift (pushed_inv h r)

/-! ### One request with the system at a time -/

/-- A request of the session's is with the system: handed to it and not answered. -/
def withSystem (s : Session) : Bool := s.asked.isSome && s.again.isNone

def isSubmit : Http.Upgrade.Action → Bool
  | .submit .. => true
  | _ => false

/-- `s'` has the request `s` has with the system, or to hand again. -/
def Keeps (s s' : Session) : Prop := s'.asked = s.asked ∧ s'.again = s.again

theorem closeWith_keeps (s : Session) (code : Nat) (reason : String) :
    Keeps s (closeWith now code reason s) := by
  unfold closeWith; split <;> exact ⟨rfl, rfl⟩

theorem failWith_keeps (s : Session) (code : Nat) : Keeps s (failWith code s) := by
  unfold failWith; split <;> exact ⟨rfl, rfl⟩

theorem sendMessage_keeps (s : Session) (m : Message) : Keeps s (sendMessage cfg m s) := by
  cases m <;>
  · unfold sendMessage
    split
    · exact ⟨rfl, rfl⟩
    · dsimp only
      split
      · exact ⟨rfl, rfl⟩
      · exact failWith_keeps { s with outbox := .empty } _

theorem absorb_keeps : ∀ (s : Session) (events : List Event), Keeps s (absorb s events)
  | _, [] => ⟨rfl, rfl⟩
  | s, .message m :: rest => absorb_keeps { s with inbox := s.inbox ++ [m] } rest
  | s, .send b :: rest => absorb_keeps { s with outbox := s.outbox ++ b } rest
  | s, .closed code :: rest => absorb_keeps { s with ended := s.ended <|> some code } rest

theorem receive_keeps (s : Session) (bytes : ByteArray) : Keeps s (receive now bytes s) := by
  unfold receive
  split
  · exact ⟨rfl, rfl⟩
  · exact absorb_keeps _ _

theorem tick_keeps (s : Session) : Keeps s (tick cfg now s) := by
  unfold tick
  repeat' split
  all_goals first | exact ⟨rfl, rfl⟩ | exact failWith_keeps _ _

theorem pushed_keeps (s : Session) (r : Http.Response) : Keeps s (pushed cfg now r s) := by
  unfold pushed
  split
  · exact sendMessage_keeps _ _
  · exact closeWith_keeps _ _ _
  · exact closeWith_keeps _ _ _

theorem offer_submits (s : Session) : ((offer now s).2.filter isSubmit).length ≤ 1 := by
  unfold offer
  repeat' split
  all_goals simp [List.filter, isSubmit]

/-- While a request is with the system, nothing more is handed to it. -/
theorem offer_withSystem {s : Session} (h : s.withSystem = true) : (offer now s).2 = [] := by
  simp only [withSystem, Bool.and_eq_true, Option.isSome_iff_exists, Option.isNone_iff_eq_none] at h
  obtain ⟨⟨a, ha⟩, hg⟩ := h
  simp [offer, ha, hg]

theorem flush_submits (s : Session) : (flush s).2.filter isSubmit = [] := by
  unfold flush
  repeat' split
  all_goals simp [isSubmit]

theorem advance_submits (s : Session) :
    (advance now s).2.filter isSubmit = (offer now s).2.filter isSubmit := by
  simp only [advance, List.filter_append, flush_submits, List.append_nil]

theorem Keeps.withSystem {s s' : Session} (h : Keeps s s') : s'.withSystem = s.withSystem := by
  simp [Session.withSystem, h.1, h.2]

/-- A socket hands the system at most one request in a step. -/
theorem step_submits (s : Session) (e : Http.Upgrade.Event) :
    ((step cfg now s e).2.filter isSubmit).length ≤ 1 := by
  cases e <;> simp only [step]
  case attached rest =>
    split
    · simp
    · simp only [List.filter_cons, isSubmit, Bool.false_eq_true, ite_false]
      rw [advance_submits]; exact offer_submits _
  all_goals (rw [advance_submits]; exact offer_submits _)

/-- While a request of the socket's is with the system, the socket hands it nothing more, but
on the system's answer to that request. -/
theorem step_withSystem {s : Session} (h : s.withSystem = true) (e : Http.Upgrade.Event)
    (he : ∀ k r, e = .answered k r → (s.asked.map (·.1)) ≠ some k) :
    (step cfg now s e).2.filter isSubmit = [] := by
  have go : ∀ s', Keeps s s' → (advance now s').2.filter isSubmit = [] := fun s' hk => by
    rw [advance_submits, offer_withSystem (hk.withSystem ▸ h)]; rfl
  cases e with
  | attached rest =>
    simp only [step]
    split
    · rfl
    · simp only [List.filter_cons, isSubmit, Bool.false_eq_true, ite_false]
      exact go _ (receive_keeps { s with attached := true, heard_ms := now, writing := true } _)
  | received bytes => exact go _ (receive_keeps _ _)
  | ended => exact go _ ⟨rfl, rfl⟩
  | broken => exact go _ ⟨rfl, rfl⟩
  | sent => exact go _ ⟨rfl, rfl⟩
  | tick => exact go _ (tick_keeps _)
  | stop => exact go _ (closeWith_keeps { s with stopping := true } _ _)
  | pushed r => exact go _ (pushed_keeps _ _)
  | answered index r =>
    apply go
    have hne := he index r rfl
    unfold answered
    split
    · rename_i k ask hs
      have : (k != index || s.again.isSome) = true := by
        simp only [hs, Option.map_some, ne_eq, Option.some.injEq] at hne
        simp [hne]
      simp only [this, ite_true]
      exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩

end Session

end Lanes.WebSocket
