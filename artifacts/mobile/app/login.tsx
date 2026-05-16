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
import { usePostAuthLogin } from "@workspace/api-client-react";

export default function LoginScreen() {
  const colors = useColors();
  const insets = useSafeAreaInsets();
  const router = useRouter();
  const { setToken } = useAuth();

  const [username, setUsername] = useState("");
  const [password, setPassword] = useState("");
  const [error, setError] = useState("");

  const login = usePostAuthLogin({
    mutation: {
      onSuccess: async (data) => {
        await setToken(data.token);
        router.replace("/app");
      },
      onError: () => {
        setError("Invalid credentials");
      },
    },
  });

  const handleLogin = () => {
    setError("");
    login.mutate({ data: { username, password } });
  };

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

        <Text style={[s.title, { color: colors.foreground }]}>ACCESS TERMINAL</Text>
        <Text style={[s.subtitle, { color: colors.mutedForeground }]}>
          Authenticate to access encrypted channels
        </Text>

        <View style={[s.card, { backgroundColor: colors.card, borderColor: colors.border }]}>
          <Text style={[s.label, { color: colors.mutedForeground }]}>IDENTIFIER</Text>
          <TextInput
            style={[s.input, { backgroundColor: colors.background, borderColor: colors.border, color: colors.foreground }]}
            value={username}
            onChangeText={setUsername}
            placeholder="username"
            placeholderTextColor={colors.mutedForeground}
            autoCapitalize="none"
            autoCorrect={false}
            testID="input-username"
          />

          <Text style={[s.label, { color: colors.mutedForeground, marginTop: 16 }]}>PASSPHRASE</Text>
          <TextInput
            style={[s.input, { backgroundColor: colors.background, borderColor: colors.border, color: colors.foreground }]}
            value={password}
            onChangeText={setPassword}
            placeholder="••••••••"
            placeholderTextColor={colors.mutedForeground}
            secureTextEntry
            testID="input-password"
          />

          {!!error && (
            <View style={[s.errorBox, { backgroundColor: "#ef444420", borderColor: "#ef444440" }]}>
              <Feather name="alert-circle" size={14} color={colors.destructive} />
              <Text style={[s.errorText, { color: colors.destructive }]}>{error}</Text>
            </View>
          )}

          <TouchableOpacity
            style={[s.btn, { backgroundColor: colors.primary }, login.isPending && s.btnDisabled]}
            onPress={handleLogin}
            disabled={login.isPending}
            testID="button-submit"
          >
            {login.isPending ? (
              <ActivityIndicator color={colors.background} size="small" />
            ) : (
              <Text style={[s.btnText, { color: colors.background }]}>AUTHENTICATE</Text>
            )}
          </TouchableOpacity>
        </View>

        <TouchableOpacity onPress={() => router.push("/register")} style={s.link}>
          <Text style={[s.linkText, { color: colors.mutedForeground }]}>
            No account?{" "}
            <Text style={{ color: colors.primary }}>REQUEST CLEARANCE</Text>
          </Text>
        </TouchableOpacity>

        <View style={[s.securityNote, { borderColor: colors.border, backgroundColor: colors.card }]}>
          <Feather name="lock" size={12} color={colors.primary} />
          <Text style={[s.securityText, { color: colors.mutedForeground }]}>
            Your private keys never leave this device
          </Text>
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
    securityNote: { flexDirection: "row", alignItems: "center", gap: 8, borderWidth: 1, padding: 12 },
    securityText: { fontFamily: "Inter_400Regular", fontSize: 11, flex: 1 },
  });
