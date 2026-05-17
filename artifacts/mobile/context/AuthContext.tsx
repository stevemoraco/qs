import React, { createContext, useContext, useState, useEffect, useCallback } from "react";
import AsyncStorage from "@react-native-async-storage/async-storage";
import * as SecureStore from "expo-secure-store";
import { setAuthTokenGetter } from "@workspace/api-client-react";

const TOKEN_KEY = "qs_token";
const AUTH_HANDLE_KEY = "qs_auth_handle";
const LAST_HANDLE_KEY = "qs_last_handle";
const DEVICE_PASSCODE_KEY = "qs_device_passcode";
const KEM_SK_KEY = "qs_kem_sk";
const KEM_PK_KEY = "qs_kem_pk";
const DSA_SK_KEY = "qs_dsa_sk";
const DSA_PK_KEY = "qs_dsa_pk";
const SECRET_KEYS = [TOKEN_KEY, AUTH_HANDLE_KEY, DEVICE_PASSCODE_KEY, KEM_SK_KEY, KEM_PK_KEY, DSA_SK_KEY, DSA_PK_KEY];

const secureStoreOptions: SecureStore.SecureStoreOptions = {
  keychainAccessible: SecureStore.WHEN_UNLOCKED_THIS_DEVICE_ONLY,
};

async function isSecureStoreAvailable(): Promise<boolean> {
  try {
    return await SecureStore.isAvailableAsync();
  } catch {
    return false;
  }
}

async function getSecret(key: string): Promise<string | null> {
  if (!(await isSecureStoreAvailable())) return null;
  const secureValue = await SecureStore.getItemAsync(key);
  if (secureValue !== null) return secureValue;

  const legacyValue = await AsyncStorage.getItem(key);
  if (legacyValue !== null) {
    await SecureStore.setItemAsync(key, legacyValue, secureStoreOptions);
    await AsyncStorage.removeItem(key);
  }
  return legacyValue;
}

async function setSecret(key: string, value: string): Promise<void> {
  if (!(await isSecureStoreAvailable())) {
    throw new Error("Secure device storage is unavailable.");
  }
  await SecureStore.setItemAsync(key, value, secureStoreOptions);
  await AsyncStorage.removeItem(key);
}

async function deleteSecret(key: string): Promise<void> {
  if (await isSecureStoreAvailable()) {
    await SecureStore.deleteItemAsync(key);
  }
  await AsyncStorage.removeItem(key);
}

async function migrateLegacySecrets(): Promise<void> {
  if (!(await isSecureStoreAvailable())) return;
  await Promise.all(SECRET_KEYS.map((key) => getSecret(key).then(() => undefined)));
}

type AuthContextType = {
  token: string | null;
  isAuthenticated: boolean;
  isLoading: boolean;
  setToken: (t: string) => Promise<void>;
  getAuthHandle: () => Promise<string | null>;
  setAuthHandle: (h: string) => Promise<void>;
  getLastHandle: () => Promise<string | null>;
  setLastHandle: (h: string) => Promise<void>;
  getDevicePasscode: () => Promise<string | null>;
  setDevicePasscode: (p: string) => Promise<void>;
  clearAuth: () => Promise<void>;
  storeKeyPair: (kemSk: string, kemPk: string, dsaSk: string, dsaPk: string) => Promise<void>;
  getKemSecretKey: () => Promise<string | null>;
  getKemPublicKey: () => Promise<string | null>;
  getDsaSecretKey: () => Promise<string | null>;
  getDsaPublicKey: () => Promise<string | null>;
};

const AuthContext = createContext<AuthContextType | null>(null);

export function AuthProvider({ children }: { children: React.ReactNode }) {
  const [token, setTokenState] = useState<string | null>(null);
  const [isLoading, setIsLoading] = useState(true);

  useEffect(() => {
    let mounted = true;
    (async () => {
      try {
        await migrateLegacySecrets();
        const t = await getSecret(TOKEN_KEY);
        if (mounted) setTokenState(t);
      } finally {
        if (mounted) setIsLoading(false);
      }
    })();
    return () => {
      mounted = false;
    };
  }, []);

  useEffect(() => {
    setAuthTokenGetter(async () => {
      return await getSecret(TOKEN_KEY);
    });
  }, []);

  const setToken = useCallback(async (t: string) => {
    await setSecret(TOKEN_KEY, t);
    setTokenState(t);
  }, []);

  const getAuthHandle = useCallback(() => getSecret(AUTH_HANDLE_KEY), []);

  const setAuthHandle = useCallback(async (h: string) => {
    await setSecret(AUTH_HANDLE_KEY, h);
  }, []);

  const getLastHandle = useCallback(async () => {
    const handle = await AsyncStorage.getItem(LAST_HANDLE_KEY);
    if (handle && /^[a-f0-9]{64}$/.test(handle)) {
      await AsyncStorage.removeItem(LAST_HANDLE_KEY);
      return null;
    }
    return handle;
  }, []);

  const setLastHandle = useCallback(async (h: string) => {
    await AsyncStorage.setItem(LAST_HANDLE_KEY, h);
  }, []);

  const getDevicePasscode = useCallback(() => getSecret(DEVICE_PASSCODE_KEY), []);

  const setDevicePasscode = useCallback(async (p: string) => {
    await setSecret(DEVICE_PASSCODE_KEY, p);
  }, []);

  const clearAuth = useCallback(async () => {
    await deleteSecret(TOKEN_KEY);
    await deleteSecret(AUTH_HANDLE_KEY);
    setTokenState(null);
  }, []);

  const storeKeyPair = useCallback(async (kemSk: string, kemPk: string, dsaSk: string, dsaPk: string) => {
    await Promise.all([
      setSecret(KEM_SK_KEY, kemSk),
      setSecret(KEM_PK_KEY, kemPk),
      setSecret(DSA_SK_KEY, dsaSk),
      setSecret(DSA_PK_KEY, dsaPk),
    ]);
  }, []);

  const getKemSecretKey = useCallback(() => getSecret(KEM_SK_KEY), []);
  const getKemPublicKey = useCallback(() => getSecret(KEM_PK_KEY), []);
  const getDsaSecretKey = useCallback(() => getSecret(DSA_SK_KEY), []);
  const getDsaPublicKey = useCallback(() => getSecret(DSA_PK_KEY), []);

  return (
    <AuthContext.Provider
      value={{
        token,
        isAuthenticated: !!token,
        isLoading,
        setToken,
        getAuthHandle,
        setAuthHandle,
        getLastHandle,
        setLastHandle,
        getDevicePasscode,
        setDevicePasscode,
        clearAuth,
        storeKeyPair,
        getKemSecretKey,
        getKemPublicKey,
        getDsaSecretKey,
        getDsaPublicKey,
      }}
    >
      {children}
    </AuthContext.Provider>
  );
}

export function useAuth() {
  const ctx = useContext(AuthContext);
  if (!ctx) throw new Error("useAuth must be used inside AuthProvider");
  return ctx;
}
