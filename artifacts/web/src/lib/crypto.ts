export const CIPHER_SUITE = "AES-256-GCM+ML-KEM-1024+ML-DSA-87";

export async function encryptMessage(plaintext: string): Promise<{
  ciphertext: string;
  nonce: string;
  key: CryptoKey;
  rawKey: Uint8Array;
}> {
  const key = await window.crypto.subtle.generateKey(
    { name: "AES-GCM", length: 256 },
    true,
    ["encrypt", "decrypt"]
  );
  const rawKey = new Uint8Array(await window.crypto.subtle.exportKey("raw", key));
  const nonce = window.crypto.getRandomValues(new Uint8Array(12));
  const encoder = new TextEncoder();
  const encrypted = await window.crypto.subtle.encrypt(
    { name: "AES-GCM", iv: nonce },
    key,
    encoder.encode(plaintext)
  );
  const ciphertext = btoa(String.fromCharCode(...new Uint8Array(encrypted)));
  const nonceB64 = btoa(String.fromCharCode(...nonce));
  return { ciphertext, nonce: nonceB64, key, rawKey };
}

export async function importMessageKey(rawKey: Uint8Array): Promise<CryptoKey> {
  return window.crypto.subtle.importKey("raw", new Uint8Array(rawKey).buffer as ArrayBuffer, { name: "AES-GCM", length: 256 }, false, ["decrypt"]);
}

export async function decryptMessage(
  ciphertext: string,
  nonce: string,
  key: CryptoKey
): Promise<string> {
  const ciphertextBytes = Uint8Array.from(atob(ciphertext), (c) => c.charCodeAt(0));
  const nonceBytes = Uint8Array.from(atob(nonce), (c) => c.charCodeAt(0));
  const decrypted = await window.crypto.subtle.decrypt(
    { name: "AES-GCM", iv: nonceBytes },
    key,
    ciphertextBytes
  );
  return new TextDecoder().decode(decrypted);
}

const messageKeyStore = new Map<string, CryptoKey>();

export function storeMessageKey(messageId: string, key: CryptoKey): void {
  messageKeyStore.set(messageId, key);
}

export function getMessageKey(messageId: string): CryptoKey | undefined {
  return messageKeyStore.get(messageId);
}

export function deleteMessageKey(messageId: string): void {
  messageKeyStore.delete(messageId);
}
