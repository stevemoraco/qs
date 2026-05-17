import { Router, type IRouter } from "express";
import { versionAuditPayload } from "../lib/version-context";

const router: IRouter = Router();

router.get("/version", (_req, res) => {
  const audit = versionAuditPayload();
  res.json({
    ...audit,
    runtime: {
      node: process.version,
      platform: process.platform,
      arch: process.arch,
      pid: process.pid,
      replit: {
        replId: process.env["REPL_ID"] ?? null,
        replSlug: process.env["REPL_SLUG"] ?? null,
        replOwner: process.env["REPL_OWNER"] ?? null,
        devDomain: process.env["REPLIT_DEV_DOMAIN"] ?? null,
      },
    },
    attestations: {
      serverHardwareOs: {
        status: "not_available",
        reason: "This Replit runtime does not expose a hardware-backed TPM/TEE attestation document to the app.",
      },
      clientHardwareOs: {
        status: "client_reported_only",
        reason: "Browser clients can report WebAuthn/WebCrypto capabilities, but hardware/OS attestation requires platform attestation APIs and cannot be proven by JavaScript alone.",
      },
      sourceIntegrity: {
        status: audit.runningState.serverBootMatchesCurrentGit ? "matched_boot_repository_digest" : "mismatch_or_unrestarted_server",
        bootRepoSha256: audit.git.boot.repoSha256,
        currentRepoSha256: audit.git.current.repoSha256,
      },
    },
  });
});

export default router;
