import { readFile } from "node:fs/promises";
import path from "node:path";

const root = path.resolve(import.meta.dirname, "..", "..");

type Check = {
  name: string;
  pass: boolean;
};

function has(source: string, snippets: string[]): boolean {
  return snippets.every((snippet) => source.includes(snippet));
}

const [chatApp, offlineVault, pwaLib, authLib] = await Promise.all([
  readFile(path.join(root, "artifacts/web/src/pages/ChatApp.tsx"), "utf8"),
  readFile(path.join(root, "artifacts/web/src/lib/offline-vault.ts"), "utf8"),
  readFile(path.join(root, "artifacts/web/src/lib/pwa.ts"), "utf8"),
  readFile(path.join(root, "artifacts/web/src/lib/auth.ts"), "utf8"),
]);

const clearEphemeralSecretsBody = authLib.match(/export function clearEphemeralSecrets\(\): void \{([\s\S]*?)\n\}/)?.[1] ?? "";

const checks: Check[] = [
  {
    name: "send path queues encrypted outbox entries when network send fails",
    pass: has(chatApp, [
      "enqueueOutbox",
      "outboxEntryToMessage",
      "qs-offline-outbox-changed",
      "data-testid=\"offline-outbox-status\"",
      "apiReachable",
      "const canReachServer = online || await apiReachable()",
      "Server did not accept the message. It is still queued and will retry. ${errorMessage(err)}",
    ]),
  },
  {
    name: "send path signs message package and requires recipient wrapped keys",
    pass: has(chatApp, [
      "recipientEncryptedKeys",
      "signature",
      "signMessagePayload",
      "button-send",
    ]),
  },
  {
    name: "send path wraps each user message key for all linked devices",
    pass: has(chatApp, [
      "getTrustedKeyBundles",
      "/api/keys/",
      "/devices",
      "wrapMessageKeyForUserDevices",
      "wrapMessageKeyForCurrentUserDevices",
      "encodeWrappedKeys",
      "return unique.length === 1 ? unique[0] : unique",
      "function sendRecipientEncryptedKeys(keys: RecipientEncryptedKeys): SendRecipientEncryptedKeys {\n  return keys as SendRecipientEncryptedKeys;\n}",
      "recipientEncryptedKeySignatureVariants",
    ]),
  },
  {
    name: "queued message flush repairs signing key metadata and never blocks later entries",
    pass: has(chatApp, [
      "senderDsaPublicKeyForSignedPayload",
      "entry.senderDsaPublicKey ?? await senderDsaPublicKeyForSignedPayload",
      "Queued message flush failed",
      "continue;",
    ]),
  },
  {
    name: "reveal path verifies sender signature before decrypting non-legacy messages",
    pass:
      has(chatApp, [
        "verifyMessageSignature",
        "const verified = await verifyMessageSignature(room.id, msg)",
        "Message signature could not be verified.",
        "activeRevealRef",
        "forceHideRevealedMsg",
      ]) &&
      chatApp.indexOf("const verified = await verifyMessageSignature(room.id, msg)") < chatApp.indexOf("decryptMessage(msg.ciphertext"),
  },
  {
    name: "reveal plaintext persists through mouse hover and clears on release, blur, and page hide",
    pass: has(chatApp, [
      "onPointerUp",
      "onPointerCancel",
      "onPointerLeave",
      "onScroll={handleMessagesScroll}",
      "activeRevealRef.current?.input === \"mouse\" && !activeRevealRef.current.released",
      "activeReveal.released = true",
      "document.addEventListener(\"visibilitychange\"",
      "window.addEventListener(\"blur\"",
    ]),
  },
  {
    name: "reveal cleanup preserves local decrypt keys for read-your-own messages",
    pass:
      clearEphemeralSecretsBody.includes("clearPrivateKeyCache()") &&
      !clearEphemeralSecretsBody.includes("localStorage.removeItem(KEM_SK_KEY)") &&
      !clearEphemeralSecretsBody.includes("localStorage.removeItem(DSA_SK_KEY)") &&
      chatApp.includes("await unwrapMessageKeyForMe(msg.recipientEncryptedKeys[currentUserId])") &&
      chatApp.includes("normalizeWrappedKeyCandidates"),
  },
  {
    name: "offline vault has durable stores for rooms, messages, members, keys, and outbox",
    pass: has(offlineVault, [
      "ROOMS_STORE",
      "MESSAGES_STORE",
      "MEMBERS_STORE",
      "KEY_BUNDLES_STORE",
      "OUTBOX_STORE",
      "enqueueOutbox",
      "getOutboxEntries",
      "deleteOutboxEntry",
    ]),
  },
  {
    name: "push subscription client rejects missing browser support and invalid VAPID keys",
    pass: has(pwaLib, [
      "Service workers are not supported in this browser.",
      "Push notifications are not supported in this browser.",
      "isLikelyP256PublicKey",
      "Server push key is invalid",
    ]),
  },
];

let failed = 0;
for (const check of checks) {
  if (!check.pass) failed += 1;
  console.log(`${check.pass ? "ok" : "not ok"} - ${check.name}`);
}
if (failed > 0) process.exitCode = 1;
