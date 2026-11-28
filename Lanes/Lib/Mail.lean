/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Lib.Mail.Basic
public import Lanes.Lib.Mail.Message

/-!
# Mail

Messages of RFC 5322 written for any relay (`Lanes/Lib/Mail/Message.lean`). A root of its own,
not in `import Lanes`: a program that sends no mail builds none of it.
-/
