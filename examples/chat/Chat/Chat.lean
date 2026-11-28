import Lanes

/-!
# A chat room

The spec, the actor and its proofs. Each member is a WebSocket, known by the id its opening
request entered with. A line one member says is sent to every member, its sender included, in
the step that takes it; joining and leaving tell everyone how many are here. The room holds at
most `Config.members_max` members, and a member that would be one more is refused.
-/

namespace Chat

open Lanes

abbrev ReqId := Nat

lanes_data inductive Request where
  /-- A socket asks to join. -/
  | join (req : ReqId)
  /-- The member `socket` says a line. -/
  | say (req socket : ReqId) (line : String)
  /-- The member `socket` has gone. -/
  | leave (req socket : ReqId)
  deriving DecidableEq, Repr, Hashable

lanes_data inductive Reply where
  | accepted
  | full
  /-- The request is taken. -/
  | taken
  /-- A line for the member the output names. -/
  | line (text : String)
  deriving DecidableEq, Repr, Hashable

lanes_data structure Out where
  req : ReqId
  reply : Reply
  deriving DecidableEq, Repr, Hashable

structure Config where
  /-- Members at once; one more is answered `full` (rule 2.6). -/
  members_max : Nat := 100

abbrev sig : Signature := Server.sig Request Out

/-- The members, in the order they joined. -/
abbrev State := List ReqId

def here (members : State) : List Out :=
  members.map fun m => ⟨m, .line s!"{members.length} here"⟩

/-- The spec, and the implementation, as the `Server` behaviour runs it. -/
def service (config : Config) : Service sig.In sig.Out State where
  init := []
  step members
    | .join req =>
      if req ∈ members then (members, [])
      else if config.members_max ≤ members.length then (members, [⟨req, .full⟩])
      else
        let members := members ++ [req]
        (members, ⟨req, .accepted⟩ :: here members)
    | .say req socket line =>
      (members, ⟨req, .taken⟩ :: if socket ∈ members then members.map (⟨·, .line line⟩) else [])
    | .leave req socket =>
      let members := members.erase socket
      (members, ⟨req, .taken⟩ :: here members)

abbrev system (config : Config) : System sig :=
  Server.system (service config)

/-- The room stays within its bound and holds each member once. -/
def Bounded (config : Config) (members : State) : Prop :=
  members.length ≤ config.members_max ∧ members.Nodup

theorem step_bounded (config : Config) (members : State) (msg : Request)
    (h : Bounded config members) : Bounded config ((service config).step members msg).1 := by
  obtain ⟨hl, hn⟩ := h
  cases msg with
  | join req =>
    simp only [service]
    split
    · exact ⟨hl, hn⟩
    · split
      · exact ⟨hl, hn⟩
      · rename_i hm hf
        refine ⟨by simp; omega, ?_⟩
        exact List.nodup_append.2 ⟨hn, by simp, by simp only [List.mem_singleton]; rintro a ha b rfl rfl; exact hm ha⟩
  | say => exact ⟨hl, hn⟩
  | leave req socket =>
    exact ⟨Nat.le_trans (List.length_erase_le ..) hl, hn.erase _⟩

theorem bounded (config : Config) :
    (Server.actor (service config)).Invariant (Bounded config) :=
  Actor.Inductive.invariant
    ⟨by simp [Server.actor, service, Bounded], fun _ s msg h => step_bounded config s msg h,
      fun _ _ h => h⟩

/-- A line a member says is taken, and sent to every member, its sender included, each once,
in the order they joined; nothing else is sent. -/
theorem step_say (config : Config) (members : State) {req socket : ReqId} {line : String}
    (h : socket ∈ members) :
    (service config).step members (.say req socket line)
      = (members, ⟨req, .taken⟩ :: members.map (⟨·, .line line⟩)) := by
  simp [service, h]

/-- A line from a socket that is not a member is taken and sent to nobody. -/
theorem step_say_stranger (config : Config) (members : State) {req socket : ReqId} {line : String}
    (h : socket ∉ members) :
    (service config).step members (.say req socket line) = (members, [⟨req, .taken⟩]) := by
  simp [service, h]

/-- A member that leaves is no longer one, and is sent nothing more. -/
theorem step_leave (config : Config) (members : State) {req socket : ReqId}
    (h : members.Nodup) :
    socket ∉ ((service config).step members (.leave req socket)).1 := by
  simp only [service]
  exact h.not_mem_erase

end Chat
