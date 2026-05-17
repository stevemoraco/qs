import { ml_dsa87 } from "@noble/post-quantum/ml-dsa.js";
import { ml_kem1024 } from "@noble/post-quantum/ml-kem.js";
import { db, roomsTable, usersTable } from "@workspace/db";
import { createCipheriv, createDecipheriv, randomBytes as nodeRandomBytes } from "crypto";
import { inArray } from "drizzle-orm";

const CIPHER_SUITE = "AES-256-GCM+ML-KEM-1024+ML-DSA-87";

type AuthResponse = {
  token: string;
  user: { id: string; kemPublicKey: string; dsaPublicKey: string };
};

type Room = { id: string };
type Message = {
  id: string;
  ciphertext: string;
  nonce: string;
  recipientEncryptedKeys: Record<string, string | string[]>;
};

function b64(bytes: Uint8Array): string {
  return Buffer.from(bytes).toString("base64");
}

function unb64(value: string): Uint8Array {
  return new Uint8Array(Buffer.from(value, "base64"));
}

function randomBytes(length: number): Uint8Array {
  return new Uint8Array(nodeRandomBytes(length));
}

function aesGcmEncrypt(key: Uint8Array, nonce: Uint8Array, plaintext: Uint8Array): Uint8Array {
  const cipher = createCipheriv("aes-256-gcm", Buffer.from(key), Buffer.from(nonce));
  const ciphertext = Buffer.concat([cipher.update(plaintext), cipher.final()]);
  return new Uint8Array(Buffer.concat([ciphertext, cipher.getAuthTag()]));
}

function aesGcmDecrypt(key: Uint8Array, nonce: Uint8Array, ciphertextAndTag: Uint8Array): Uint8Array {
  const input = Buffer.from(ciphertextAndTag);
  const ciphertext = input.subarray(0, -16);
  const tag = input.subarray(-16);
  const decipher = createDecipheriv("aes-256-gcm", Buffer.from(key), Buffer.from(nonce));
  decipher.setAuthTag(tag);
  return new Uint8Array(Buffer.concat([decipher.update(ciphertext), decipher.final()]));
}

function stableJson(value: unknown): string {
  if (value === null || typeof value !== "object") return JSON.stringify(value);
  if (Array.isArray(value)) return `[${value.map(stableJson).join(",")}]`;
  return `{${Object.keys(value as Record<string, unknown>)
    .sort()
    .map((key) => `${JSON.stringify(key)}:${stableJson((value as Record<string, unknown>)[key])}`)
    .join(",")}}`;
}

function messageSignaturePayload(input: {
  roomId: string;
  senderId: string;
  ciphertext: string;
  nonce: string;
  algorithm: string;
  recipientEncryptedKeys: Record<string, string | string[]>;
}): Uint8Array {
  return new TextEncoder().encode(stableJson({
    v: 1,
    purpose: "quantumshield.chat.message",
    roomId: input.roomId,
    senderId: input.senderId,
    ciphertext: input.ciphertext,
    nonce: input.nonce,
    algorithm: input.algorithm,
    recipientEncryptedKeys: input.recipientEncryptedKeys,
  }));
}

function wrapMessageKey(kemPublicKey: Uint8Array, rawMessageKey: Uint8Array): string {
  const { cipherText, sharedSecret } = ml_kem1024.encapsulate(kemPublicKey);
  const nonce = randomBytes(12);
  const wrappedKey = aesGcmEncrypt(sharedSecret, nonce, rawMessageKey);
  return JSON.stringify({
    kemCiphertext: b64(cipherText),
    nonce: b64(nonce),
    wrappedKey: b64(wrappedKey),
  });
}

function unwrapMessageKey(kemSecretKey: Uint8Array, wrapped: string): Uint8Array {
  const parsed = JSON.parse(wrapped) as { kemCiphertext: string; nonce: string; wrappedKey: string };
  const sharedSecret = ml_kem1024.decapsulate(unb64(parsed.kemCiphertext), kemSecretKey);
  return aesGcmDecrypt(sharedSecret, unb64(parsed.nonce), unb64(parsed.wrappedKey));
}

function encryptText(text: string): { ciphertext: string; nonce: string; key: Uint8Array } {
  const key = randomBytes(32);
  const nonce = randomBytes(12);
  return {
    ciphertext: b64(aesGcmEncrypt(key, nonce, new TextEncoder().encode(text))),
    nonce: b64(nonce),
    key,
  };
}

function decryptText(ciphertext: string, nonce: string, key: Uint8Array): string {
  return new TextDecoder().decode(aesGcmDecrypt(key, unb64(nonce), unb64(ciphertext)));
}

function decryptWithAnyWrappedKey(
  ciphertext: string,
  nonce: string,
  kemSecretKey: Uint8Array,
  wrappedKeys: string[],
): string {
  let lastError: unknown = null;
  for (const wrappedKey of wrappedKeys) {
    try {
      return decryptText(ciphertext, nonce, unwrapMessageKey(kemSecretKey, wrappedKey));
    } catch (error) {
      lastError = error;
    }
  }
  throw lastError instanceof Error ? lastError : new Error("No wrapped key could be decrypted");
}

async function request<T>(baseUrl: string, path: string, options: RequestInit = {}): Promise<T> {
  const res = await fetch(`${baseUrl}${path}`, {
    ...options,
    headers: {
      "content-type": "application/json",
      ...(options.headers ?? {}),
    },
  });
  const text = await res.text();
  const data = text ? JSON.parse(text) : null;
  if (!res.ok) {
    throw new Error(`${options.method ?? "GET"} ${path} failed: ${res.status} ${text}`);
  }
  return data as T;
}

async function main(): Promise<void> {
  process.env.QS_DISABLE_BACKGROUND_WORKERS = "1";
  const app = (await import("../artifacts/api-server/src/app")).default;
  const server = app.listen(0);
  const address = server.address();
  if (!address || typeof address === "string") throw new Error("API test server did not bind a TCP port");
  const baseUrl = `http://127.0.0.1:${address.port}/api`;
  const createdUserIds: string[] = [];
  const createdRoomIds: string[] = [];

  try {
    const register = async (label: string) => {
      const kem = ml_kem1024.keygen();
      const dsa = ml_dsa87.keygen();
      const auth = await request<AuthResponse>(baseUrl, "/auth/register", {
        method: "POST",
        body: JSON.stringify({
          primaryCode: `e2e-${label}-${Date.now().toString(36)}-${Math.random().toString(36).slice(2, 8)}`,
          passcode: `passcode-${label}-123456`,
          kemPublicKey: b64(kem.publicKey),
          dsaPublicKey: b64(dsa.publicKey),
        }),
      });
      createdUserIds.push(auth.user.id);
      const uploadKey = async (kemPublicKey: Uint8Array) => {
        await request(baseUrl, "/keys/upload", {
          method: "POST",
          headers: { authorization: `Bearer ${auth.token}` },
          body: JSON.stringify({
            kemPublicKey: b64(kemPublicKey),
            dsaPublicKey: b64(dsa.publicKey),
            kemSignature: b64(ml_dsa87.sign(kemPublicKey, dsa.secretKey)),
          }),
        });
      };
      await uploadKey(kem.publicKey);
      return { auth, kem, dsa, uploadKey };
    };

    const alice = await register("alice");
    const bob = await register("bob");
    const aliceSecondDeviceKem = ml_kem1024.keygen();
    await alice.uploadKey(aliceSecondDeviceKem.publicKey);

    const aliceDevices = await request<{ bundles: Array<{ kemPublicKey: string }> }>(
      baseUrl,
      `/keys/${alice.auth.user.id}/devices`,
      { headers: { authorization: `Bearer ${alice.auth.token}` } },
    );
    if (new Set(aliceDevices.bundles.map((bundle) => bundle.kemPublicKey)).size < 2) {
      throw new Error("Alice device fanout did not return both linked device KEM keys");
    }

    const room = await request<Room>(baseUrl, "/rooms", {
      method: "POST",
      headers: { authorization: `Bearer ${alice.auth.token}` },
      body: JSON.stringify({
        type: "direct",
        memberIds: [bob.auth.user.id],
        ttlSeconds: 300,
        ttlMode: "after_view",
        deliveryFuzzSeconds: 0,
      }),
    });
    createdRoomIds.push(room.id);

    const plaintext = `hello e2e ${Date.now()}`;
    const encrypted = encryptText(plaintext);
    const recipientEncryptedKeys = {
      [alice.auth.user.id]: aliceDevices.bundles.map((bundle) => wrapMessageKey(unb64(bundle.kemPublicKey), encrypted.key)),
      [bob.auth.user.id]: wrapMessageKey(bob.kem.publicKey, encrypted.key),
    };
    const signature = b64(ml_dsa87.sign(messageSignaturePayload({
      roomId: room.id,
      senderId: alice.auth.user.id,
      ciphertext: encrypted.ciphertext,
      nonce: encrypted.nonce,
      algorithm: CIPHER_SUITE,
      recipientEncryptedKeys,
    }), alice.dsa.secretKey));

    await request<Message>(baseUrl, `/rooms/${room.id}/messages`, {
      method: "POST",
      headers: { authorization: `Bearer ${alice.auth.token}` },
      body: JSON.stringify({
        ciphertext: encrypted.ciphertext,
        nonce: encrypted.nonce,
        algorithm: CIPHER_SUITE,
        signature,
        senderDsaPublicKey: b64(alice.dsa.publicKey),
        recipientEncryptedKeys,
      }),
    });

    const [aliceMessage] = await request<Message[]>(baseUrl, `/rooms/${room.id}/messages`, {
      headers: { authorization: `Bearer ${alice.auth.token}` },
    });
    const [bobMessage] = await request<Message[]>(baseUrl, `/rooms/${room.id}/messages`, {
      headers: { authorization: `Bearer ${bob.auth.token}` },
    });
    if (!aliceMessage || !bobMessage) throw new Error("Message did not load for both room members");

    const aliceWrappedKeys = aliceMessage.recipientEncryptedKeys[alice.auth.user.id];
    if (!Array.isArray(aliceWrappedKeys) || aliceWrappedKeys.length < 2) {
      throw new Error("Alice message did not persist one wrapped key per linked Alice device");
    }
    const aliceSecondPlaintext = decryptWithAnyWrappedKey(
      aliceMessage.ciphertext,
      aliceMessage.nonce,
      aliceSecondDeviceKem.secretKey,
      aliceWrappedKeys,
    );
    const bobPlaintext = decryptText(
      bobMessage.ciphertext,
      bobMessage.nonce,
      unwrapMessageKey(bob.kem.secretKey, bobMessage.recipientEncryptedKeys[bob.auth.user.id] as string),
    );

    if (aliceSecondPlaintext !== plaintext) throw new Error("Alice second device could not decrypt Alice's sent message");
    if (bobPlaintext !== plaintext) throw new Error("Bob could not decrypt Alice's message before expiry");

    console.log("ok - live API encrypted send/decrypt works for sender second device and recipient");
  } finally {
    if (createdRoomIds.length > 0) {
      await db.delete(roomsTable).where(inArray(roomsTable.id, createdRoomIds));
    }
    if (createdUserIds.length > 0) {
      await db.delete(usersTable).where(inArray(usersTable.id, createdUserIds));
    }
    await new Promise<void>((resolve, reject) => server.close((err) => err ? reject(err) : resolve()));
  }
}

await main();
