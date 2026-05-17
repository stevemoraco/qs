import { readFile } from "node:fs/promises";
import path from "node:path";

const root = path.resolve(import.meta.dirname, "..", "..");

type Check = {
  name: string;
  pass: boolean;
  detail?: string;
};

function includesAll(source: string, snippets: string[]): boolean {
  return snippets.every((snippet) => source.includes(snippet));
}

function report(checks: Check[]): void {
  const failed = checks.filter((check) => !check.pass);
  for (const check of checks) {
    console.log(`${check.pass ? "ok" : "not ok"} - ${check.name}${check.detail ? ` (${check.detail})` : ""}`);
  }
  if (failed.length > 0) {
    process.exitCode = 1;
  }
}

const [pushRoute, roomsRoute, messagesRoute, authRoute, keysRoute] = await Promise.all([
  readFile(path.join(root, "artifacts/api-server/src/routes/push.ts"), "utf8"),
  readFile(path.join(root, "artifacts/api-server/src/routes/rooms.ts"), "utf8"),
  readFile(path.join(root, "artifacts/api-server/src/routes/messages.ts"), "utf8"),
  readFile(path.join(root, "artifacts/api-server/src/routes/auth.ts"), "utf8"),
  readFile(path.join(root, "artifacts/api-server/src/routes/keys.ts"), "utf8"),
]);

const checks: Check[] = [
  {
    name: "push subscribe rejects arbitrary endpoints before persistence",
    pass:
      includesAll(pushRoute, [
        "function isValidPushEndpoint",
        "url.protocol !== \"https:\"",
        "PUSH_HOST_PATTERNS.some",
        "Endpoint is not a recognized Web Push service",
      ]) &&
      pushRoute.indexOf("!isValidPushEndpoint(endpoint)") < pushRoute.indexOf("db.insert(pushSubscriptionsTable)"),
  },
  {
    name: "push delivery removes expired subscriptions",
    pass: includesAll(pushRoute, [
      "statusCode === 404 || statusCode === 410",
      "db.delete(pushSubscriptionsTable)",
      "Deleted expired push subscription",
    ]),
  },
  {
    name: "room creation rejects after-send fuzz windows that outlive TTL",
    pass: includesAll(roomsRoute, [
      "effectiveTtlMode === \"after_send\"",
      "effectiveDeliveryFuzz >= effectiveTtl",
      "Delivery fuzz must be shorter than after-send TTL",
    ]),
  },
  {
    name: "message send validates fuzz, recipient keys, signatures, and idempotency",
    pass: includesAll(messagesRoute, [
      "validDurationSeconds(room.deliveryFuzzSeconds, MAX_DELIVERY_FUZZ_SECONDS)",
      "recipientEncryptedKeys must include exactly one wrapped key for each current room member",
      "verifiesMessageSignature",
      "eq(messagesTable.signature, signature!)",
      "randomInt(0, fuzzSeconds + 1)",
      "notificationPayload",
    ]),
  },
  {
    name: "message send accepts multi-device wrapped keys per member",
    pass: includesAll(messagesRoute, [
      "type RecipientEncryptedKeyValue = string | string[]",
      "function isValidWrappedKeyValue",
      "Array.isArray(value)",
      "recipientEncryptedKeys",
    ]) && includesAll(keysRoute, [
      "router.get(\"/keys/:userId/devices\"",
      "seenKemKeys",
      "bundles",
    ]),
  },
  {
    name: "message send accepts authenticated embedded device signing keys",
    pass: includesAll(messagesRoute, [
      "senderDsaCandidates.add(senderDsaPublicKey)",
      "const verifiedSenderDsaPublicKey",
      "INVALID_MESSAGE_SIGNATURE",
      "senderDsaPublicKey: senderDsaPublicKey ?? sender?.dsaPublicKey ?? null",
    ]),
  },
  {
    name: "experimental quorum decay purges wrapped keys on read/timer",
    pass: includesAll(messagesRoute, [
      "EXPERIMENTAL_QUORUM_DECAY",
      "purgeExpiredMessageKeys",
      "recipientEncryptedKeys: null",
      "decayAttestation",
      "await purgeExpiredMessageKeys(readAttestation)",
    ]),
  },
  {
    name: "passkey handle recovery avoids account enumeration and expired handles",
    pass: includesAll(authRoute, [
      "genericPasskeyError",
      "!handleState.active || (handleState.expiresAt && handleState.expiresAt <= new Date())",
      "allowCredentials.length === 0",
      "Passkey challenge expired. Try again.",
      "or(isNull(identityCodesTable.expiresAt), gt(identityCodesTable.expiresAt, new Date()))",
    ]),
  },
  {
    name: "API responses and generated client bypass browser caching",
    pass: includesAll(authRoute, [
      "genericPasskeyError",
    ]) && includesAll(await readFile(path.join(root, "artifacts/api-server/src/app.ts"), "utf8"), [
      "app.disable(\"etag\")",
      "Cache-Control",
      "no-store, max-age=0",
      "app.use(\"/api\"",
    ]) && includesAll(await readFile(path.join(root, "lib/api-client-react/src/custom-fetch.ts"), "utf8"), [
      "function isApiRequest",
      "init.cache ?? (isApiRequest(input) ? \"no-store\" : undefined)",
    ]),
  },
];

report(checks);
