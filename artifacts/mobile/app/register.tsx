import { useState } from "react";
import {
  View,
  Text,
  TextInput,
  TouchableOpacity,
  StyleSheet,
  KeyboardAvoidingView,
  Platform,
  ScrollView,
  ActivityIndicator,
} from "react-native";
import { useRouter } from "expo-router";
import { useSafeAreaInsets } from "react-native-safe-area-context";
import { Feather } from "@expo/vector-icons";
import { useColors } from "@/hooks/useColors";
import { useAuth } from "@/context/AuthContext";
import { usePostAuthRegister, usePostKeysUpload } from "@workspace/api-client-react";

type Step = "idle" | "keygen" | "register" | "upload" | "done";

const STEP_LABELS: Record<Step, string> = {
  idle: "CREATE IDENTITY",
  keygen: "GENERATING PQ KEYS...",
  register: "REGISTERING IDENTITY...",
  upload: "UPLOADING KEY BUNDLE...",
  done: "COMPLETE",
};

function uint8ToBase64(arr: Uint8Array): string {
  let binary = "";
  for (let i = 0; i < arr.length; i++) {
    binary += String.fromCharCode(arr[i]);
  }
  return btoa(binary);
}

export default function RegisterScreen() {
  const colors = useColors();
  const insets = useSafeAreaInsets();
  const router = useRouter();
  const { setToken, storeKeyPair } = useAuth();

  const [username, setUsername] = useState("");
  const [displayName, setDisplayName] = useState("");
  const [passcode, setPasscode] = useState("");
  const [error, setError] = useState("");
  const [step, setStep] = useState<Step>("idle");

  const register = usePostAuthRegister();
  const uploadKeys = usePostKeysUpload();

  const handleRegister = async () => {
    setError("");
    try {
      setStep("keygen");
      const { ml_kem1024 } = await import("@noble/post-quantum/ml-kem.js");
      const { ml_dsa87 } = await import("@noble/post-quantum/ml-dsa.js");
      const kem = ml_kem1024.keygen();
      const dsa = ml_dsa87.keygen();

      const kemPkB64 = uint8ToBase64(kem.publicKey);
      const kemSkB64 = uint8ToBase64(kem.secretKey);
      const dsaPkB64 = uint8ToBase64(dsa.publicKey);
      const dsaSkB64 = uint8ToBase64(dsa.secretKey);

      setStep("register");
      const authData = await register.mutateAsync({
        data: {
          username,
          password: passcode,
          displayName: displayName || undefined,
          kemPublicKey: kemPkB64,
          dsaPublicKey: dsaPkB64,
        },
      });

      await storeKeyPair(kemSkB64, kemPkB64, dsaSkB64, dsaPkB64);
      await setToken(authData.token);

      setStep("upload");
      const kemSig = ml_dsa87.sign(kem.publicKey, dsa.secretKey);
      await uploadKeys.mutateAsync({
        data: {
          kemPublicKey: kemPkB64,
          dsaPublicKey: dsaPkB64,
          kemSignature: uint8ToBase64(kemSig),
        },
      });

      setStep("done");
      router.replace("/app");
    } catch {
      setStep("idle");
      setError("Registration failed. Username or passcode may be invalid.");
    }
  };

  const isLoading = step !== "idle";
  const s = makeStyles(colors);

  return (
    <KeyboardAvoidingView
      style={[s.root, { backgroundColor: colors.background }]}
      behavior={Platform.OS === "ios" ? "padding" : "height"}
    >
      <ScrollView
        contentContainerStyle={[s.scroll, { paddingTop: insets.top + 40, paddingBottom: insets.bottom + 24 }]}
        keyboardShouldPersistTaps="handled"
      >
        <View style={s.header}>
          <View style={[s.iconBox, { backgroundColor: colors.primary }]}>
            <Feather name="shield" size={20} color={colors.background} />
          </View>
          <Text style={[s.brand, { color: colors.foreground }]}>QUANTUMSHIELD</Text>
        </View>

        <Text style={[s.title, { color: colors.foreground }]}>REQUEST CLEARANCE</Text>
        <Text style={[s.subtitle, { color: colors.mutedForeground }]}>
          Post-quantum key pairs are generated locally on this device
        </Text>

        <View style={[s.card, { backgroundColor: colors.card, borderColor: colors.border }]}>
          <Text style={[s.label, { color: colors.mutedForeground }]}>IDENTIFIER</Text>
          <TextInput
            style={[s.input, { backgroundColor: colors.background, borderColor: colors.border, color: colors.foreground }]}
            value={username}
            onChangeText={setUsername}
            placeholder="username (min 3 chars)"
            placeholderTextColor={colors.mutedForeground}
            autoCapitalize="none"
            autoCorrect={false}
            editable={!isLoading}
            testID="input-username"
          />

          <Text style={[s.label, { color: colors.mutedForeground, marginTop: 16 }]}>DISPLAY NAME (OPTIONAL)</Text>
          <TextInput
            style={[s.input, { backgroundColor: colors.background, borderColor: colors.border, color: colors.foreground }]}
            value={displayName}
            onChangeText={setDisplayName}
            placeholder="Display name"
            placeholderTextColor={colors.mutedForeground}
            editable={!isLoading}
          />

          <Text style={[s.label, { color: colors.mutedForeground, marginTop: 16 }]}>PASSCODE</Text>
          <TextInput
            style={[s.input, { backgroundColor: colors.background, borderColor: colors.border, color: colors.foreground }]}
            value={passcode}
            onChangeText={setPasscode}
            placeholder="passcode (min 8 characters)"
            placeholderTextColor={colors.mutedForeground}
            secureTextEntry
            editable={!isLoading}
            testID="input-password"
          />

          {!!error && (
            <View style={[s.errorBox, { backgroundColor: "#ef444420", borderColor: "#ef444440" }]}>
              <Feather name="alert-circle" size={14} color={colors.destructive} />
              <Text style={[s.errorText, { color: colors.destructive }]}>{error}</Text>
            </View>
          )}

          {isLoading && (
            <View style={[s.infoBox, { backgroundColor: `${colors.primary}15`, borderColor: `${colors.primary}40` }]}>
              <ActivityIndicator color={colors.primary} size="small" />
              <Text style={[s.infoText, { color: colors.primary }]}>{STEP_LABELS[step]}</Text>
            </View>
          )}

          <TouchableOpacity
            style={[s.btn, { backgroundColor: colors.primary }, isLoading && s.btnDisabled]}
            onPress={handleRegister}
            disabled={isLoading}
            testID="button-submit"
          >
            {isLoading ? (
              <ActivityIndicator color={colors.background} size="small" />
            ) : (
              <Text style={[s.btnText, { color: colors.background }]}>{STEP_LABELS[step]}</Text>
            )}
          </TouchableOpacity>
        </View>

        <TouchableOpacity onPress={() => router.push("/login")} style={s.link}>
          <Text style={[s.linkText, { color: colors.mutedForeground }]}>
            Already registered?{" "}
            <Text style={{ color: colors.primary }}>AUTHENTICATE</Text>
          </Text>
        </TouchableOpacity>

        <View style={[s.card, { backgroundColor: `${colors.primary}10`, borderColor: `${colors.primary}30` }]}>
          {[
            "ML-KEM-1024 keys generated on-device",
            "ML-DSA-87 identity keys generated locally",
            "Private keys stored only in secure storage",
          ].map((note) => (
            <View key={note} style={s.checkRow}>
              <Feather name="check-circle" size={12} color={colors.primary} />
              <Text style={[s.checkText, { color: colors.mutedForeground }]}>{note}</Text>
            </View>
          ))}
        </View>
      </ScrollView>
    </KeyboardAvoidingView>
  );
}

const makeStyles = (colors: ReturnType<typeof useColors>) =>
  StyleSheet.create({
    root: { flex: 1 },
    scroll: { flexGrow: 1, paddingHorizontal: 24 },
    header: { flexDirection: "row", alignItems: "center", gap: 10, marginBottom: 40 },
    iconBox: { width: 32, height: 32, alignItems: "center", justifyContent: "center" },
    brand: { fontFamily: "Inter_700Bold", fontSize: 11, letterSpacing: 5 },
    title: { fontFamily: "Inter_700Bold", fontSize: 24, letterSpacing: -0.5, marginBottom: 8 },
    subtitle: { fontFamily: "Inter_400Regular", fontSize: 13, marginBottom: 28, lineHeight: 20 },
    card: { borderWidth: 1, padding: 20, marginBottom: 24 },
    label: { fontFamily: "Inter_500Medium", fontSize: 10, letterSpacing: 3, marginBottom: 8 },
    input: {
      borderWidth: 1,
      paddingHorizontal: 12,
      paddingVertical: 12,
      fontFamily: "Inter_400Regular",
      fontSize: 14,
    },
    errorBox: { flexDirection: "row", alignItems: "center", gap: 8, borderWidth: 1, padding: 10, marginTop: 12 },
    errorText: { fontFamily: "Inter_400Regular", fontSize: 12, flex: 1 },
    infoBox: { flexDirection: "row", alignItems: "center", gap: 8, borderWidth: 1, padding: 10, marginTop: 12 },
    infoText: { fontFamily: "Inter_500Medium", fontSize: 12, flex: 1 },
    btn: {
      paddingVertical: 14,
      alignItems: "center",
      justifyContent: "center",
      marginTop: 20,
      flexDirection: "row",
      gap: 8,
    },
    btnDisabled: { opacity: 0.5 },
    btnText: { fontFamily: "Inter_700Bold", fontSize: 11, letterSpacing: 3 },
    link: { alignItems: "center", marginBottom: 20 },
    linkText: { fontFamily: "Inter_400Regular", fontSize: 13 },
    checkRow: { flexDirection: "row", alignItems: "center", gap: 8, marginBottom: 8 },
    checkText: { fontFamily: "Inter_400Regular", fontSize: 11, flex: 1 },
  });
