/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes

/-!
Sign-in with GitHub: an OAuth app, which gives no ID token. The user is known by calling
GitHub's API with the access token: `GET /user` for the user's number, `id`, which never changes
(the `login` may), and `GET /user/emails`, which the scope `user:email` allows, for the primary
address and whether GitHub verified it. `read` makes an identity of the two answers, and refuses
answers of other shapes rather than guess. The name shown is the user's `name`, which may be
`null`, or else the `login`.
-/

namespace GitHub

open Lanes Lanes.OAuth

def issuer : String := "https://github.com"

/-- Whether a member of an object is `true`; absent or of another type is not. -/
def yes (j : Json) (key : String) : Bool := (j.getObjValAs? Bool key).toOption == some true

/-- An identity of the answers of `GET /user` and `GET /user/emails`, in that order. -/
def read : List Json → Except String Identity
  | [user, emails] => do
    let id ← user.getObjValAs? Nat "id"
    let all ← emails.getArr?
    let primary := all.toList.find? (yes · "primary")
    let email := primary.bind fun e => (e.getObjValAs? String "email").toOption
    let name := ((user.getObjValAs? String "name").toOption.bind DisplayName.clean).orElse
      fun _ => (user.getObjValAs? String "login").toOption.bind DisplayName.clean
    return { issuer, subject := toString id, email,
             emailVerified := email.isSome && primary.any (yes · "verified"), name }
  | _ => .error "the answers of /user and /user/emails expected"

def provider : Provider where
  name := "github"
  authorize := "https://github.com/login/oauth/authorize"
  token := "https://github.com/login/oauth/access_token"
  scopes := ["read:user", "user:email"]
  source := .userApi ["https://api.github.com/user", "https://api.github.com/user/emails"] read

end GitHub
