import { Router } from "express";
import { createTimeQuorumAttestation } from "../lib/time-quorum";

const router = Router();

router.get("/time/attestation", async (_req, res) => {
  res.json(await createTimeQuorumAttestation());
});

export default router;
