/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lanes.Services.Oidc.GitHub
import Lanes

/-!
GitHub's answers in the shapes its REST documentation gives them, written by hand: none was
recorded from GitHub (`docs/decisions/D72-sign-in-with-oauth.md`).
-/

namespace Checks.GitHub

open Lanes Lanes.OAuth

def parse (text : String) : Json := (Json.parse text).toOption.getD .null

def user : Json := parse "{\"login\":\"octocat\",\"id\":1,\"node_id\":\"MDQ6VXNlcjE=\",\
  \"type\":\"User\",\"site_admin\":false,\"name\":\"monalisa octocat\",\"email\":\"octocat@github.com\"}"

def emails : Json := parse "[{\"email\":\"old@example.com\",\"verified\":true,\"primary\":false,\
  \"visibility\":null},{\"email\":\"octocat@github.com\",\"verified\":true,\"primary\":true,\
  \"visibility\":\"public\"}]"

def unverified : Json := parse "[{\"email\":\"octocat@github.com\",\"verified\":false,\
  \"primary\":true,\"visibility\":\"public\"}]"

/-- The name `read` gives the answers. -/
def shown (answers : List Json) : Option String :=
  ((GitHub.read answers).toOption.bind (·.name)).map (·.val)

def long : String := String.ofList (List.replicate 100 'x')

def tests : List (String × Bool) :=
  [ ("github: the user is GitHub's number for them, with the primary address, verified",
      (GitHub.read [user, emails]).toOption == some {
        issuer := "https://github.com", subject := "1", email := some "octocat@github.com",
        emailVerified := true, name := DisplayName.of? "monalisa octocat" }),
    ("github: with no name, the login is the name shown",
      shown [parse "{\"login\":\"octocat\",\"id\":1,\"name\":null}", emails] == some "octocat"),
    ("github: a name is cleaned and cut to its bound, and a blank one gives the login",
      shown [parse "{\"login\":\"o\",\"id\":1,\"name\":\"  a\\u0000b\\u202ec  \"}", emails] == some "abc"
        && (shown [parse s!"\{\"login\":\"o\",\"id\":1,\"name\":\"{long}\"}", emails]).map (·.length)
          == some DisplayName.maxChars
        && shown [parse "{\"login\":\"o\",\"id\":1,\"name\":\" \"}", emails] == some "o"),
    ("github: an address GitHub has not verified is said to be unverified",
      (GitHub.read [user, unverified]).toOption.any fun id => !id.emailVerified),
    ("github: no primary address is no address",
      (GitHub.read [user, parse "[]"]).toOption.any fun id => id.email.isNone && !id.emailVerified),
    ("github: answers of other shapes are refused",
      [ [user], [user, emails, emails], [parse "{\"id\":\"1\"}", emails],
        [parse "{\"login\":\"octocat\"}", emails], [user, parse "{}"], [parse "[]", emails] ].all
        fun answers => (GitHub.read answers) matches .error _),
    ("github: the token endpoint's answer is read, in JSON as asked",
      (Tokens.read 200 "{\"access_token\":\"gho_16C7e42F292c6912E7710c838347Ae178B4a\",\
        \"scope\":\"read:user,user:email\",\"token_type\":\"bearer\"}".toUTF8) matches .ok _),
    ("github: its error, sent with status 200, is a refusal",
      (Tokens.read 200 "{\"error\":\"bad_verification_code\",\"error_description\":\"The code \
        passed is incorrect or expired.\"}".toUTF8) matches .error (.token "bad_verification_code")) ]

end Checks.GitHub
