import { useState, type ComponentProps } from "react";
import {
  View,
  Text,
  TouchableOpacity,
  StyleSheet,
  KeyboardAvoidingView,
  Platform,
  ScrollView,
  ActivityIndicator,
  Linking,
  TextInput,
} from "react-native";
import { useRouter } from "expo-router";
import { useSafeAreaInsets } from "react-native-safe-area-context";
import { Feather } from "@expo/vector-icons";
import * as LocalAuthentication from "expo-local-authentication";
import { useColors } from "@/hooks/useColors";
import { useAuth } from "@/context/AuthContext";
import { usePostAuthLogin } from "@workspace/api-client-react";

const GITHUB_URL = "https://github.com/stevemoraco/qs";

function normalizeCodeInput(value: string): string {
  return value.trim().replace(/^[@#]+/, "").toLowerCase();
}

const PRIVACY_FEATURES: Array<{ icon: ComponentProps<typeof Feather>["name"]; label: string }> = [
  { icon: "camera", label: "Front-camera detection for nearby recording devices" },
  { icon: "mouse-pointer", label: "Messages decrypt only while held, one at a time" },
  { icon: "user-x", label: "Usernames and rooms stay codenamed until reveal" },
  { icon: "clock", label: "TTL keys are purged so old ciphertext becomes noise" },
  { icon: "eye-off", label: "Blur and background shields hide secure content" },
  { icon: "monitor", label: "Screenshot, screen-capture, and print friction" },
  { icon: "key", label: "Alias and invite codes scope discovery and access" },
  { icon: "lock", label: "Only the handle is typed; device verification unlocks local access" },
  { icon: "shield", label: "Fresh device sessions are issued and invalidated on logout" },
];

async function verifyDevice(promptMessage: string): Promise<void> {
  const hasHardware = await LocalAuthentication.hasHardwareAsync();
  const isEnrolled = await LocalAuthentication.isEnrolledAsync();
  if (!hasHardware || !isEnrolled) {
    throw new Error("Face ID or device biometrics are not set up.");
  }

  const result = await LocalAuthentication.authenticateAsync({
    promptMessage,
    fallbackLabel: "Use device passcode",
    disableDeviceFallback: false,
  });
  if (!result.success) throw new Error("Device verification was not completed.");
}

export default function LoginScreen() {
  const colors = useColors();
  const insets = useSafeAreaInsets();
  const router = useRouter();
  const { getDevicePasscode, setAuthHandle, setDevicePasscode, setToken } = useAuth();

  const [handle, setHandle] = useState("");
  const [error, setError] = useState("");
  const [linkCode, setLinkCode] = useState("");
  const [isLinking, setIsLinking] = useState(false);

  const login = usePostAuthLogin({
    mutation: {
      onSuccess: async (data) => {
        await setToken(data.token);
        await setAuthHandle(data.authHandle);
        router.replace("/app");
      },
      onError: () => {
        setError("Invalid handle or passcode");
      },
    },
  });

  const handleLogin = async () => {
    setError("");
    const normalizedHandle = normalizeCodeInput(handle);
    if (!normalizedHandle) {
      setError("Enter your handle.");
      return;
    }
    const passcode = await getDevicePasscode();
    if (!passcode) {
      setError("No local device access key found. Link this device with an invite.");
      return;
    }
    login.mutate({ data: { handle: normalizedHandle, passcode } });
  };

  const isLoading = login.isPending;
  const s = makeStyles(colors);

  const generateDevicePasscode = () => {
    const bytes = new Uint8Array(32);
    const getRandomValues = globalThis.crypto?.getRandomValues?.bind(globalThis.crypto);
    if (!getRandomValues) throw new Error("Secure random generator unavailable.");
    getRandomValues(bytes);
    return Array.from(bytes, (b) => b.toString(16).padStart(2, "0")).join("");
  };

  const handleLinkDevice = async () => {
    setError("");
    const code = normalizeCodeInput(linkCode);
    if (!code) {
      setError("Enter an invite code to link this device. Handles are for discovery only.");
      return;
    }
    try {
      setIsLinking(true);
      await verifyDevice("Link QuantumShield device");
      const passcode = generateDevicePasscode();
      const url = Platform.OS === "web" ? "/api/auth/link-device" : `https://${process.env.EXPO_PUBLIC_DOMAIN}/api/auth/link-device`;
      const res = await fetch(url, {
        method: "POST",
        headers: { "content-type": "application/json" },
        body: JSON.stringify({ code, passcode, deviceLabel: Platform.OS }),
      });
      const data = await res.json();
      if (!res.ok) throw new Error(data?.error ?? "Could not link this device");
      await setToken(data.token);
      await setAuthHandle(data.authHandle);
      await setDevicePasscode(passcode);
      router.replace("/app");
    } catch (err: unknown) {
      setError(err instanceof Error ? err.message : "Could not link this device with that invite.");
    } finally {
      setIsLinking(false);
    }
  };

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

        <Text style={[s.title, { color: colors.foreground }]}>ACCESS TERMINAL</Text>
        <Text style={[s.subtitle, { color: colors.mutedForeground }]}>Authenticate to access encrypted channels</Text>

        <View style={[s.card, { backgroundColor: colors.card, borderColor: colors.border }]}>
          <Text style={[s.label, { color: colors.mutedForeground }]}>HANDLE</Text>
          <TextInput
            style={[s.input, { backgroundColor: colors.background, borderColor: colors.border, color: colors.foreground }]}
            value={handle}
            onChangeText={setHandle}
            placeholder="@your-handle"
            placeholderTextColor={colors.mutedForeground}
            autoCapitalize="none"
            autoComplete="username"
            testID="input-handle"
          />

          {!!error && (
            <View style={[s.errorBox, { backgroundColor: "#ef444420", borderColor: "#ef444440" }]}> 
              <Feather name="alert-circle" size={14} color={colors.destructive} />
              <Text style={[s.errorText, { color: colors.destructive }]}>{error}</Text>
            </View>
          )}

          <TouchableOpacity
            style={[s.btn, { backgroundColor: colors.primary }, isLoading && s.btnDisabled]}
            onPress={handleLogin}
            disabled={isLoading}
            testID="button-submit"
          >
            {isLoading ? (
              <ActivityIndicator color={colors.background} size="small" />
            ) : (
              <Text style={[s.btnText, { color: colors.background }]}>LOG IN</Text>
            )}
          </TouchableOpacity>
        </View>

        <TouchableOpacity onPress={() => router.push("/register")} style={s.link}>
          <Text style={[s.linkText, { color: colors.mutedForeground }]}>No account? <Text style={{ color: colors.primary }}>CREATE HANDLE</Text></Text>
        </TouchableOpacity>

        <View style={[s.card, { backgroundColor: colors.card, borderColor: colors.border }]}>
          <Text style={[s.ethosLabel, { color: colors.primary }]}>LINK THIS DEVICE</Text>
          <Text style={[s.securityText, { color: colors.mutedForeground, marginBottom: 12 }]}>Use a one-use invite code from an existing device. Public handles are for chat discovery, not login.</Text>
          <TextInput
            style={[s.input, { backgroundColor: colors.background, borderColor: colors.border, color: colors.foreground }]}
            value={linkCode}
            onChangeText={setLinkCode}
            placeholder="invite code"
            placeholderTextColor={colors.mutedForeground}
            autoCapitalize="none"
            testID="input-link-code"
          />
          <TouchableOpacity
            style={[s.btn, { backgroundColor: colors.primary }, isLinking && s.btnDisabled]}
            onPress={handleLinkDevice}
            disabled={isLinking}
            testID="button-link-device"
          >
            {isLinking ? <ActivityIndicator color={colors.background} size="small" /> : <Text style={[s.btnText, { color: colors.background }]}>LINK WITH INVITE</Text>}
          </TouchableOpacity>
        </View>

        <View style={[s.securityNote, { borderColor: colors.border, backgroundColor: colors.card }]}> 
          <Feather name="lock" size={12} color={colors.primary} />
          <Text style={[s.securityText, { color: colors.mutedForeground }]}>Your private keys never leave this device</Text>
        </View>

        <View style={[s.ethosCard, { borderColor: `${colors.primary}40`, backgroundColor: colors.card }]}> 
          <Text style={[s.ethosLabel, { color: colors.primary }]}>ETHOS</Text>
          <Text style={[s.ethosText, { color: colors.mutedForeground }]}>What is the most secure ideal form of truly ephemeral digital communication? QuantumShield is a working experiment to answer that with software communities can audit, improve, and rely on.</Text>
          <TouchableOpacity
            onPress={() => Linking.openURL(GITHUB_URL)}
            style={[s.githubBtn, { borderColor: colors.border }]}
            testID="button-github"
          >
            <Feather name="github" size={14} color={colors.primary} />
            <Text style={[s.githubText, { color: colors.foreground }]}>VIEW GITHUB</Text>
            <Feather name="external-link" size={12} color={colors.mutedForeground} />
          </TouchableOpacity>
        </View>

        <View style={[s.privacyCard, { borderColor: colors.border, backgroundColor: colors.card }]}> 
          <Text style={[s.ethosLabel, { color: colors.primary }]}>PRIVACY FEATURES</Text>
          {PRIVACY_FEATURES.map((feature) => (
            <View key={feature.label} style={s.featureRow}>
              <Feather name={feature.icon} size={14} color={colors.primary} />
              <Text style={[s.featureText, { color: colors.mutedForeground }]}>{feature.label}</Text>
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
    input: { borderWidth: 1, paddingHorizontal: 12, paddingVertical: 12, fontFamily: "Inter_400Regular", fontSize: 14 },
    errorBox: { flexDirection: "row", alignItems: "center", gap: 8, borderWidth: 1, padding: 10, marginTop: 12 },
    errorText: { fontFamily: "Inter_400Regular", fontSize: 12, flex: 1 },
    btn: { paddingVertical: 14, alignItems: "center", justifyContent: "center", marginTop: 20, flexDirection: "row", gap: 8 },
    btnDisabled: { opacity: 0.5 },
    btnText: { fontFamily: "Inter_700Bold", fontSize: 11, letterSpacing: 3 },
    link: { alignItems: "center", marginBottom: 20 },
    linkText: { fontFamily: "Inter_400Regular", fontSize: 13 },
    securityNote: { flexDirection: "row", alignItems: "center", gap: 8, borderWidth: 1, padding: 12 },
    securityText: { fontFamily: "Inter_400Regular", fontSize: 11, flex: 1 },
    ethosCard: { borderWidth: 1, padding: 16, marginTop: 14 },
    ethosLabel: { fontFamily: "Inter_700Bold", fontSize: 10, letterSpacing: 3, marginBottom: 8 },
    ethosText: { fontFamily: "Inter_400Regular", fontSize: 12, lineHeight: 19 },
    githubBtn: { marginTop: 14, borderWidth: 1, paddingVertical: 12, alignItems: "center", justifyContent: "center", flexDirection: "row", gap: 8 },
    githubText: { fontFamily: "Inter_700Bold", fontSize: 10, letterSpacing: 2.5 },
    privacyCard: { borderWidth: 1, padding: 16, marginTop: 14, gap: 12 },
    featureRow: { flexDirection: "row", alignItems: "flex-start", gap: 10 },
    featureText: { fontFamily: "Inter_400Regular", fontSize: 11, lineHeight: 17, flex: 1 },
  });
