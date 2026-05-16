import React, { createContext, useContext, useState, useEffect, useCallback } from "react";
import AsyncStorage from "@react-native-async-storage/async-storage";
import { setAuthTokenGetter } from "@workspace/api-client-react";

const TOKEN_KEY = "qs_token";
const KEM_SK_KEY = "qs_kem_sk";
const KEM_PK_KEY = "qs_kem_pk";
const DSA_SK_KEY = "qs_dsa_sk";
const DSA_PK_KEY = "qs_dsa_pk";

type AuthContextType = {
  token: string | null;
  isAuthenticated: boolean;
  isLoading: boolean;
  setToken: (t: string) => Promise<void>;
  clearAuth: () => Promise<void>;
  storeKeyPair: (kemSk: string, kemPk: string, dsaSk: string, dsaPk: string) => Promise<void>;
  getKemPublicKey: () => Promise<string | null>;
  getDsaPublicKey: () => Promise<string | null>;
};

const AuthContext = createContext<AuthContextType | null>(null);

export function AuthProvider({ children }: { children: React.ReactNode }) {
  const [token, setTokenState] = useState<string | null>(null);
  const [isLoading, setIsLoading] = useState(true);

  useEffect(() => {
    AsyncStorage.getItem(TOKEN_KEY).then((t) => {
      setTokenState(t);
      setIsLoading(false);
    });
  }, []);

  useEffect(() => {
    setAuthTokenGetter(async () => {
      return await AsyncStorage.getItem(TOKEN_KEY);
    });
  }, []);

  const setToken = useCallback(async (t: string) => {
    await AsyncStorage.setItem(TOKEN_KEY, t);
    setTokenState(t);
  }, []);

  const clearAuth = useCallback(async () => {
    await AsyncStorage.multiRemove([TOKEN_KEY, KEM_SK_KEY, KEM_PK_KEY, DSA_SK_KEY, DSA_PK_KEY]);
    setTokenState(null);
  }, []);

  const storeKeyPair = useCallback(async (kemSk: string, kemPk: string, dsaSk: string, dsaPk: string) => {
    await AsyncStorage.multiSet([
      [KEM_SK_KEY, kemSk],
      [KEM_PK_KEY, kemPk],
      [DSA_SK_KEY, dsaSk],
      [DSA_PK_KEY, dsaPk],
    ]);
  }, []);

  const getKemPublicKey = useCallback(() => AsyncStorage.getItem(KEM_PK_KEY), []);
  const getDsaPublicKey = useCallback(() => AsyncStorage.getItem(DSA_PK_KEY), []);

  return (
    <AuthContext.Provider
      value={{
        token,
        isAuthenticated: !!token,
        isLoading,
        setToken,
        clearAuth,
        storeKeyPair,
        getKemPublicKey,
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
