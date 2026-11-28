# S3

Status: **checked**. For any S3-compatible store (AWS, MinIO), named virtual-hosted or by path.

- **Client**: pure calls and the reading of answers (`Basic.lean`, `Xml.lean`), browser uploads
  by a form under a policy (`Post.lean`, proved in `PostSound.lean`) and multipart uploads
  (`Multipart.lean`); the IO, which signs with the core's Signature Version 4 and only performs,
  is `IO/Client.lean`.
- **Model**: the object store, `Lanes/Outside/ObjectStore.lean`, a shape of the core; and S3's
  multipart uploads, `MultipartModel.lean`, built from the core's `Lanes/Outside/Rpc.lean`. The
  multipart model is here, not in the core, because only S3 has it.
- **Oracle**: moto, an emulator. `oracles/moto/run.sh` runs the calls, the forms and the
  multipart flow against moto's S3 and checks the runs against the models
  (`oracles/moto/s3.jsonl`, `oracles/moto/s3-post.jsonl`, `oracles/moto/s3-multipart.jsonl`);
  CI runs it nightly. The signing is compared with botocore (`oracles/botocore`) and the XML
  reader with Go's (`oracles/go/xml`) on every pull request.
- **Fake**: `Testing.lean`, the fake S3 that tests run against, which checks each signature.
  It is here rather than in `Lanes/Testing/` because the core never imports a service.
