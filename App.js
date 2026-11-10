import React, { useCallback, useEffect, useMemo, useRef, useState } from 'react';
import {
  View, Text, Pressable, ScrollView, Modal, Platform, StyleSheet, SafeAreaView, useWindowDimensions,
  useColorScheme, Animated, Image, Settings, AppState, Alert, Share, FlatList,
} from 'react-native';
import { StatusBar } from 'expo-status-bar';
import * as Clipboard from 'expo-clipboard';
import { GlassView, isLiquidGlassAvailable } from 'expo-glass-effect';
import { iniciarFonte } from './fonte';
import { criarHistorico } from './historico';
import { criarCerebro } from './cerebro';

/* ---------- memória do celular ---------- */
const store = {
  get(k, def) {
    try { if (Platform.OS === 'ios') { const v = Settings.get(k); return v ? JSON.parse(v) : def; } } catch (e) {}
    return def;
  },
  set(k, v) {
    try { if (Platform.OS === 'ios') Settings.set({ [k]: JSON.stringify(v) }); } catch (e) {}
  },
};
const HIST = criarHistorico(store, 'cb');
const CER = criarCerebro({ store, tag: 'cerebro' });

let glassOK = false;
try { glassOK = Platform.OS === 'ios' && isLiquidGlassAvailable(); } catch (e) { glassOK = false; }
function Glass({ style, children, dark, interactive }) {
  const base = dark ? '255,255,255' : '60,60,67';
  if (glassOK) {
    return (
      <GlassView style={[style, { overflow: 'hidden' }]} glassEffectStyle="regular"
        tintColor={`rgba(${base},0.16)`} isInteractive={!!interactive}>{children}</GlassView>
    );
  }
  return <View style={[style, { backgroundColor: `rgba(${base},0.14)`, overflow: 'hidden' }]}>{children}</View>;
}

const pad = (n) => String(n).padStart(2, '0');
const hm = (t) => { const d = new Date(t); return `${pad(d.getHours())}:${pad(d.getMinutes())}`; };
const hms = (t) => { const d = new Date(t); return `${pad(d.getHours())}:${pad(d.getMinutes())}:${pad(d.getSeconds())}`; };
const corPedra = (n) => (n === 0 ? '#ffffff' : n <= 7 ? '#f12c4c' : '#262f3c');

const COR_TIPO = {
  info: '#9aa0a6', regime: '#ffb020', branco: '#ffffff', seca: '#ff9f1a', chute: '#4da3ff',
  ok: '#2ecc71', erro: '#ff5a5f', estrat: '#a78bfa', resumo: '#9aa0a6', descoberta: '#2ecc71',
};

/* ---------- faixa das 10 últimas pedras ---------- */
function Faixa({ pedras, ultimoId, slotW, dark }) {
  const shown = pedras.slice(-11);
  const shift = useRef(new Animated.Value(0)).current;
  useEffect(() => {
    shift.setValue(0);
    if (shown.length > 10) Animated.timing(shift, { toValue: -slotW, duration: 380, useNativeDriver: true }).start();
  }, [ultimoId]);
  const box = slotW - 6;
  return (
    <View style={{ width: slotW * 10, overflow: 'hidden', alignSelf: 'center', minHeight: box + 16 }}>
      <Animated.View style={{ flexDirection: 'row', transform: [{ translateX: shift }] }}>
        {shown.map((s, i) => {
          const op = i === 0 && shown.length > 10
            ? shift.interpolate({ inputRange: [-slotW, 0], outputRange: [0, 1], extrapolate: 'clamp' }) : 1;
          return (
            <Animated.View key={s.id} style={{ width: slotW, alignItems: 'center', opacity: op }}>
              <View style={{
                width: box, height: box, borderRadius: 9, backgroundColor: corPedra(s.n), alignItems: 'center',
                justifyContent: 'center', borderWidth: s.n === 0 ? 1 : 0, borderColor: 'rgba(128,128,128,0.4)',
              }}>
                {s.n === 0
                  ? <Image source={require('./fundo-logo.png')} style={{ width: box * 0.7, height: box * 0.7 }} resizeMode="contain" />
                  : <Text style={{ color: '#fff', fontWeight: '800', fontSize: 13 }}>{s.n}</Text>}
              </View>
              <Text style={{ color: dark ? '#b0b4ba' : '#555', fontSize: 8.5, marginTop: 3, fontWeight: '600' }}>{hm(s.t)}</Text>
            </Animated.View>
          );
        })}
      </Animated.View>
    </View>
  );
}

/* ---------- aba "Pedras" do relatório (por hora) ---------- */
function PedrasPorHora({ dark, txt, sub }) {
  const [horas, setHoras] = useState(24);
  const [abertas, setAbertas] = useState({});
  const { width } = useWindowDimensions();
  const lista = useMemo(() => {
    const agora = new Date();
    const fim = new Date(agora.getFullYear(), agora.getMonth(), agora.getDate(), agora.getHours() + 1).getTime();
    const ini = fim - horas * 3600000;
    const ped = HIST.pedrasEntre(ini, fim);
    const out = [];
    for (let h = 0; h < horas; h++) {
      const a = fim - (h + 1) * 3600000, b = a + 3600000;
      out.push({ ini: a, ped: ped.filter((p) => p.t >= a && p.t < b) });
    }
    return out;
  }, [horas]);
  const cel = Math.floor((width - 56) / 10) - 3;
  return (
    <View>
      {lista.map((h) => {
        const aberta = !!abertas[h.ini];
        const brancos = h.ped.filter((p) => p.n === 0).length;
        return (
          <View key={h.ini} style={{ marginBottom: 8 }}>
            <Pressable onPress={() => setAbertas((o) => ({ ...o, [h.ini]: !o[h.ini] }))}>
              <Glass dark={dark} style={{ borderRadius: 12, padding: 12, flexDirection: 'row', justifyContent: 'space-between' }}>
                <Text style={{ color: txt, fontWeight: '800' }}>{hm(h.ini)} – {hm(h.ini + 3600000)}</Text>
                <Text style={{ color: sub, fontWeight: '600' }}>{h.ped.length} pedras · {brancos} brancos</Text>
              </Glass>
            </Pressable>
            {aberta && (
              <View style={{ flexDirection: 'row', flexWrap: 'wrap', paddingTop: 8 }}>
                {h.ped.map((p, i) => (
                  <View key={i} style={{ width: cel, height: cel, margin: 1.5, borderRadius: 6, backgroundColor: corPedra(p.n), alignItems: 'center', justifyContent: 'center', borderWidth: p.n === 0 ? 1 : 0, borderColor: 'rgba(128,128,128,0.4)' }}>
                    <Text style={{ color: p.n === 0 ? '#111' : '#fff', fontSize: 10, fontWeight: '800' }}>{p.n}</Text>
                  </View>
                ))}
              </View>
            )}
          </View>
        );
      })}
      <Pressable onPress={() => setHoras((v) => v + 24)} style={{ padding: 12, alignItems: 'center' }}>
        <Text style={{ color: '#4da3ff', fontWeight: '800' }}>Ver mais 24 horas</Text>
      </Pressable>
    </View>
  );
}

export default function App() {
  const sys = useColorScheme();
  const dark = sys !== 'light';
  const { width: W, height: H } = useWindowDimensions();
  const txt = dark ? '#ffffff' : '#111111';
  const sub = dark ? '#b0b4ba' : '#555555';
  const slotW = Math.floor((W - 24) / 10);

  const [conectado, setConectado] = useState(false);
  const [stones, setStones] = useState([]);
  const [ultimoId, setUltimoId] = useState(0);
  const [linhas, setLinhas] = useState([]);
  const [pronto, setPronto] = useState(false);
  const [prog, setProg] = useState('');
  const [relAberto, setRelAberto] = useState(false);
  const [aba, setAba] = useState('cerebro');
  const [relTxt, setRelTxt] = useState('');
  const [aviso, setAviso] = useState('');
  const vistos = useRef(new Set());
  const seq = useRef(0);
  const lista = useRef(null);
  const perto = useRef(true);

  const avisar = (m) => { setAviso(m); setTimeout(() => setAviso(''), 2200); };
  const copiar = async (t, msg) => { try { await Clipboard.setStringAsync(t); avisar(msg || 'Copiado!'); } catch (e) { avisar('Não consegui copiar'); } };

  const aceitar = (s) => {
    const k = `${s.id}-${s.t}`;
    if (vistos.current.has(k)) return null;
    vistos.current.add(k);
    return { id: ++seq.current, n: s.n, t: s.t };
  };

  useEffect(() => {
    let vivo = true;
    HIST.carregar();
    // últimas 10 pedras guardadas
    const ult = HIST.pedrasEntre(Date.now() - 2 * 3600000, Infinity).slice(-11).map((p) => ({ id: ++seq.current, n: p.n, t: p.t }));
    setStones(ult);
    setLinhas(CER.linhas().slice(-400));
    const off = CER.aoLinha((l) => {
      if (!vivo) return;
      setLinhas((a) => [...a.slice(-399), l]);
    });
    CER.iniciar(HIST.pedrasEntre(0, Infinity), (m) => { if (vivo) setProg(m || ''); }).then(() => { if (vivo) { setPronto(true); setProg(''); } });

    iniciarFonte({
      onStatus: (v) => setConectado(v),
      onInicial: (lst) => {
        let ultimo = null;
        const novos = [];
        lst.forEach((raw) => {
          const s = aceitar(raw);
          if (s) { HIST.adicionar(s); CER.pedra(s); novos.push(s); ultimo = s; }
        });
        if (ultimo) { setStones((a) => [...a, ...novos].slice(-12)); setUltimoId(ultimo.id); }
      },
      onNova: (raw) => {
        const s = aceitar(raw);
        if (!s) return;
        HIST.adicionar(s);
        CER.pedra(s);
        setStones((a) => [...a, s].slice(-12));
        setUltimoId(s.id);
      },
    });

    const timer = setInterval(() => CER.salvar(), 20000);
    const sub2 = AppState.addEventListener('change', (e) => { if (e !== 'active') CER.salvar(true); });
    return () => { vivo = false; off(); clearInterval(timer); sub2.remove(); CER.salvar(true); };
  }, []);

  const abrirRelatorio = () => {
    CER.salvar(true);
    try { setRelTxt(CER.relatorio()); } catch (e) { setRelTxt('Erro ao montar o relatório: ' + e.message); }
    setRelAberto(true);
  };

  const exportarPedras = async () => {
    try { await Share.share({ message: HIST.exportar() }); } catch (e) { avisar('Não deu para compartilhar'); }
  };

  const itens = linhas.slice().reverse(); // mais nova em cima (lista invertida)

  const renderLinha = ({ item }) => (
    <View style={{ paddingVertical: 5, flexDirection: 'row' }}>
      <Text style={{ color: sub, fontSize: 10.5, width: 52, fontVariant: ['tabular-nums'], paddingTop: 2 }}>{hms(item.t)}</Text>
      <Text style={{ color: COR_TIPO[item.tipo] || txt, fontSize: 13.5, flex: 1, lineHeight: 18, fontWeight: item.tipo === 'descoberta' || item.tipo === 'ok' ? '700' : '500' }}>{item.txt}</Text>
    </View>
  );

  return (
    <View style={[st.root, { backgroundColor: dark ? '#000' : '#fff' }]}>
      <StatusBar style={dark ? 'light' : 'dark'} />
      <View pointerEvents="none" style={st.logoWrap}>
        <Image source={require('./fundo-logo.png')} style={{ width: W * 0.4, height: H * 0.3, opacity: 0.5 }} resizeMode="contain" />
      </View>
      <SafeAreaView style={{ flex: 1 }}>
        <View style={st.topo}>
          <Text style={{ color: txt, fontWeight: '900', fontSize: 18 }}>Cérebro</Text>
          <View style={{ flexDirection: 'row', alignItems: 'center' }}>
            {!pronto ? <Text style={{ color: sub, fontSize: 11, marginRight: 10 }}>{prog || 'carregando…'}</Text> : null}
            <View pointerEvents="none" style={[st.led, { backgroundColor: conectado ? '#2ecc71' : '#ff3b30', shadowColor: conectado ? '#2ecc71' : '#ff3b30' }]} />
          </View>
        </View>

        <Text style={{ color: sub, textAlign: 'center', fontSize: 11, fontWeight: '800', marginBottom: 8, marginTop: 4 }}>ÚLTIMAS PEDRAS</Text>
        <Faixa pedras={stones} ultimoId={ultimoId} slotW={slotW} dark={dark} />

        <Text style={{ color: sub, fontSize: 11, fontWeight: '800', marginTop: 14, marginBottom: 4, paddingHorizontal: 16 }}>O QUE O CÉREBRO ESTÁ PENSANDO</Text>
        <FlatList
          ref={lista}
          data={itens}
          inverted
          keyExtractor={(l) => String(l.id)}
          renderItem={renderLinha}
          contentContainerStyle={{ paddingHorizontal: 16, paddingBottom: 90 }}
          ListEmptyComponent={<Text style={{ color: sub, padding: 20, textAlign: 'center' }}>Aguardando pedras… o cérebro começa a falar assim que chegarem.</Text>}
        />
      </SafeAreaView>

      <View style={st.barraBaixo} pointerEvents="box-none">
        <Pressable onPress={abrirRelatorio}>
          <Glass dark={dark} interactive style={st.btnRel}>
            <Text style={{ color: txt, fontWeight: '800', fontSize: 14 }}>Relatório</Text>
          </Glass>
        </Pressable>
        <Pressable onPress={() => copiar(CER.conversaTexto(), 'Conversa copiada!')}>
          <Glass dark={dark} interactive style={st.btnRel}>
            <Text style={{ color: txt, fontWeight: '800', fontSize: 14 }}>Copiar conversa</Text>
          </Glass>
        </Pressable>
      </View>

      {aviso ? (
        <View pointerEvents="none" style={st.toast}><Text style={{ color: '#fff', fontWeight: '700' }}>{aviso}</Text></View>
      ) : null}

      <Modal visible={relAberto} animationType="slide" onRequestClose={() => setRelAberto(false)}>
        <View style={{ flex: 1, backgroundColor: dark ? '#000' : '#fff' }}>
          <SafeAreaView style={{ flex: 1 }}>
            <View style={st.topo}>
              <Text style={{ color: txt, fontWeight: '900', fontSize: 18 }}>Relatório</Text>
              <Pressable onPress={() => setRelAberto(false)} hitSlop={12}><Text style={{ color: '#4da3ff', fontWeight: '800', fontSize: 16 }}>Fechar</Text></Pressable>
            </View>
            <View style={{ flexDirection: 'row', paddingHorizontal: 16, marginBottom: 10 }}>
              {[['cerebro', 'Cérebro'], ['pedras', 'Pedras']].map(([k, nome]) => (
                <Pressable key={k} onPress={() => setAba(k)} style={{ marginRight: 8 }}>
                  <Glass dark={dark} style={{ borderRadius: 16, paddingVertical: 8, paddingHorizontal: 16, opacity: aba === k ? 1 : 0.55 }}>
                    <Text style={{ color: txt, fontWeight: '800' }}>{nome}</Text>
                  </Glass>
                </Pressable>
              ))}
            </View>
            <ScrollView contentContainerStyle={{ paddingHorizontal: 16, paddingBottom: 50 }}>
              {aba === 'cerebro' ? (
                <View>
                  <View style={{ flexDirection: 'row', flexWrap: 'wrap', marginBottom: 10 }}>
                    <Pressable onPress={() => copiar(relTxt, 'Relatório copiado!')} style={st.mini}><Text style={st.miniTxt}>Copiar relatório</Text></Pressable>
                    <Pressable onPress={() => copiar(CER.conversaTexto(), 'Conversa copiada!')} style={st.mini}><Text style={st.miniTxt}>Copiar conversa</Text></Pressable>
                    <Pressable onPress={() => { try { setRelTxt(CER.relatorio()); } catch (e) {} }} style={st.mini}><Text style={st.miniTxt}>Atualizar</Text></Pressable>
                  </View>
                  <Text selectable style={{ color: txt, fontSize: 12, lineHeight: 17, fontFamily: Platform.OS === 'ios' ? 'Menlo' : 'monospace' }}>{relTxt}</Text>
                </View>
              ) : (
                <View>
                  <View style={{ flexDirection: 'row', flexWrap: 'wrap', marginBottom: 10 }}>
                    <Pressable onPress={exportarPedras} style={st.mini}><Text style={st.miniTxt}>Compartilhar pedras</Text></Pressable>
                    <Pressable onPress={() => copiar(HIST.exportar(), 'Pedras copiadas!')} style={st.mini}><Text style={st.miniTxt}>Copiar pedras</Text></Pressable>
                  </View>
                  <Text style={{ color: sub, marginBottom: 10, fontSize: 12 }}>{HIST.total()} pedras guardadas neste celular.</Text>
                  <PedrasPorHora dark={dark} txt={txt} sub={sub} />
                </View>
              )}
            </ScrollView>
          </SafeAreaView>
        </View>
      </Modal>
    </View>
  );
}

const st = StyleSheet.create({
  root: { flex: 1 },
  logoWrap: { position: 'absolute', top: 0, left: 0, right: 0, bottom: 0, alignItems: 'center', justifyContent: 'center' },
  topo: { flexDirection: 'row', justifyContent: 'space-between', alignItems: 'center', paddingHorizontal: 16, paddingTop: Platform.OS === 'android' ? 30 : 8, paddingBottom: 6 },
  led: { width: 10, height: 10, borderRadius: 5, shadowOpacity: 0.9, shadowRadius: 5, shadowOffset: { width: 0, height: 0 } },
  barraBaixo: { position: 'absolute', left: 0, right: 0, bottom: 28, flexDirection: 'row', justifyContent: 'center' },
  btnRel: { borderRadius: 22, paddingVertical: 13, paddingHorizontal: 22, marginHorizontal: 6 },
  toast: { position: 'absolute', top: 70, alignSelf: 'center', backgroundColor: 'rgba(0,0,0,0.85)', paddingVertical: 8, paddingHorizontal: 16, borderRadius: 16 },
  mini: { backgroundColor: '#1f6feb', borderRadius: 14, paddingVertical: 8, paddingHorizontal: 14, marginRight: 8, marginBottom: 8 },
  miniTxt: { color: '#fff', fontWeight: '800', fontSize: 13 },
});
