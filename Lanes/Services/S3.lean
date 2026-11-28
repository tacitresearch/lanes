/-
Copyright (c) 2026 The Lanes Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Lanes.Services.S3.Basic
public import Lanes.Services.S3.IO.Client
public import Lanes.Services.S3.Multipart
public import Lanes.Services.S3.MultipartModel
public import Lanes.Services.S3.Post
public import Lanes.Services.S3.Xml

/-!
S3's client, for any S3-compatible store: signed calls, multipart uploads and their model, and
browser uploads by `POST` (`Lanes/Services/S3/README.md`). The fake S3 for tests is
`Lanes.Services.S3.Testing`.
-/
