// Datalogger 9 assi - app Flutter (Android)
// Legge via Bluetooth il sensore costruito e, tramite lui, i due WitMotion WT9011DCL.
import 'dart:async';
import 'dart:convert';
import 'dart:io';
import 'dart:math' as math;
import 'dart:typed_data';

import 'package:flutter/material.dart';
import 'package:flutter_blue_plus/flutter_blue_plus.dart';
import 'package:path_provider/path_provider.dart';
import 'package:share_plus/share_plus.dart';

final Guid kSvc = Guid('6e400001-b5a3-f393-e0a9-e50e24dcca9e');
final Guid kCmd = Guid('6e400002-b5a3-f393-e0a9-e50e24dcca9e');
final Guid kChr = Guid('6e400003-b5a3-f393-e0a9-e50e24dcca9e');
final Guid kFil = Guid('6e400004-b5a3-f393-e0a9-e50e24dcca9e');
final Guid kWtSvc = Guid('0000ffe5-0000-1000-8000-00805f9a34fb');
final Guid kBatSvc = Guid('0000180f-0000-1000-8000-00805f9a34fb');
final Guid kBatChr = Guid('00002a19-0000-1000-8000-00805f9a34fb');// WitMotion BLE

const int kLen = 148; // t(4) + 35 float + flags(1) + flags2(1) + pad(2)
const int kMax = 1800; // 3 minuti a 10 pacchetti al secondo
const String kHdr =
    'ms,ax,ay,az,gx,gy,gz,mx,my,mz,tempC,hPa,vibRMS,roll,pitch,yaw,batV,fHz,'
    'wt1_ax,wt1_ay,wt1_az,wt1_gx,wt1_gy,wt1_gz,wt1_roll,wt1_pitch,wt1_yaw,'
    'wt2_ax,wt2_ay,wt2_az,wt2_gx,wt2_gy,wt2_gz,wt2_roll,wt2_pitch,wt2_yaw,quotaRel_m';

void main() => runApp(const DataloggerApp());

class DataloggerApp extends StatelessWidget {
  const DataloggerApp({super.key});
  @override
  Widget build(BuildContext context) {
    return MaterialApp(
      title: 'Datalogger 9 assi',
      theme: ThemeData(colorSchemeSeed: Colors.blue, useMaterial3: true),
      darkTheme: ThemeData(colorSchemeSeed: Colors.blue, brightness: Brightness.dark, useMaterial3: true),
      home: const HomePage(),
    );
  }
}

class ChartDef {
  final String title;
  final List<int> idx;
  final List<String> names;
  final int dp;
  final bool rel;
  const ChartDef(this.title, this.idx, this.names, {this.dp = 2, this.rel = false});
}

const List<ChartDef> sensorCharts = [
  ChartDef('Accelerazione (g)', [0, 1, 2], ['X', 'Y', 'Z']),
  ChartDef('Giroscopio (°/s)', [3, 4, 5], ['X', 'Y', 'Z'], dp: 1),
  ChartDef('Magnetometro (µT)', [6, 7, 8], ['X', 'Y', 'Z'], dp: 1),
  ChartDef('Orientamento (°)', [12, 13, 14], ['Roll', 'Pitch', 'Yaw'], dp: 1),
  ChartDef('Temperatura (°C)', [9], [''], dp: 1),
  ChartDef('Pressione (hPa)', [10], [''], dp: 1),
  ChartDef('Quota relativa (m)', [35], [''], dp: 1, rel: true),
  ChartDef('Vibrazione RMS (g)', [11], [''], dp: 3),
  ChartDef('Frequenza dominante (Hz)', [16], [''], dp: 0),
];

List<ChartDef> wtCharts(int n) {
  final b = n == 1 ? 17 : 26;
  return [
    ChartDef('WT$n accelerazione (g)', [b, b + 1, b + 2], ['X', 'Y', 'Z']),
    ChartDef('WT$n giroscopio (°/s)', [b + 3, b + 4, b + 5], ['X', 'Y', 'Z'], dp: 1),
    ChartDef('WT$n angoli (°)', [b + 6, b + 7, b + 8], ['Roll', 'Pitch', 'Yaw'], dp: 1),
  ];
}

int batPct(double v) {
  const t = [
    [3.3, 0.0], [3.5, 5.0], [3.7, 20.0], [3.8, 45.0],
    [3.9, 65.0], [4.0, 80.0], [4.1, 92.0], [4.2, 100.0],
  ];
  if (v <= t[0][0]) return 0;
  for (int i = 1; i < t.length; i++) {
    if (v <= t[i][0]) {
      return (t[i - 1][1] + (t[i][1] - t[i - 1][1]) * (v - t[i - 1][0]) / (t[i][0] - t[i - 1][0])).round();
    }
  }
  return 100;
}

class HomePage extends StatefulWidget {
  const HomePage({super.key});
  @override
  State<HomePage> createState() => _HomePageState();
}

class _HomePageState extends State<HomePage> {
  BluetoothDevice? dev;
  BluetoothCharacteristic? cmdC;
  bool connected = false;
  String status = 'Non connesso';
  final Uint8List asm = Uint8List(kLen);
  int got = 0;
  final List<List<double>> buf = [];
  List<double> last = List<double>.filled(36, 0);
  int flags = 0, flags2 = 0, prevFlags = 0, shocks = 0;
  double? alt0;
  double lastAbs = 0;
  bool recOn = false;
  final List<String> rec = [];
  int windowSec = 30;
  Timer? ticker;
  String fmode = '';
  String fcur = '';
  final List<int> fbytes = [];
  List<List<String>> files = [];
  String fprog = '';
  int rng = 3;
  int rate = 200;
  double shock = 3;
  // WitMotion collegati direttamente al telefono
  bool directMode = false;
  final List<bool> wtLive = [false, false];
  final List<BluetoothDevice?> wtDev = [null, null];
  final List<List<int>> wtBuf = [<int>[], <int>[]];
  final List<int> wtCount = [0, 0];
  final List<String> wtRaw = ['', ''];
      final List<int?> wtBat = [null, null];

  Timer? directTimer;

  @override
  void initState() {
    super.initState();
    ticker = Timer.periodic(const Duration(milliseconds: 300), (_) {
      if (mounted) setState(() {});
    });
  }

  @override
  void dispose() {
    ticker?.cancel();
    directTimer?.cancel();
    dev?.disconnect();
    super.dispose();
  }

  // ---------- Bluetooth ----------
  Future<void> connectDev() async {
    setState(() => status = 'Ricerca…');
    try {
      BluetoothDevice? found;
      final sub = FlutterBluePlus.scanResults.listen((rs) {
        if (rs.isNotEmpty) found ??= rs.last.device;
      });
      await FlutterBluePlus.startScan(withServices: [kSvc], timeout: const Duration(seconds: 6));
      await FlutterBluePlus.isScanning.where((s) => s == false).first;
      await sub.cancel();
      if (found == null) {
        setState(() => status = 'Sensore non trovato');
        return;
      }
      final d = found!;
      await d.connect();
      d.connectionState.listen((s) {
        if (s == BluetoothConnectionState.disconnected && mounted) {
          setState(() {
            connected = false;
            status = 'Disconnesso';
          });
        }
      });
      final services = await d.discoverServices();
      final svc = services.firstWhere((x) => x.uuid == kSvc);
      for (final c in svc.characteristics) {
        if (c.uuid == kCmd) cmdC = c;
        if (c.uuid == kChr) {
          await c.setNotifyValue(true);
          d.cancelWhenDisconnected(c.onValueReceived.listen(onPkt));
        }
        if (c.uuid == kFil) {
          await c.setNotifyValue(true);
          d.cancelWhenDisconnected(c.onValueReceived.listen(onFile));
        }
      }
      dev = d;
      alt0 = null;
      setState(() {
        connected = true;
        status = 'Connesso a ${d.platformName}';
      });
    } catch (e) {
      setState(() => status = 'Errore: $e');
    }
  }

  Future<void> disconnectDev() async {
    await dev?.disconnect();
    for (final d in wtDev) {
      await d?.disconnect();
    }
    directTimer?.cancel();
    setState(() {
      directMode = false;
      wtLive[0] = false;
      wtLive[1] = false;
    });
  }

  // ---------- WitMotion collegato direttamente al telefono ----------
  Future<void> connectWtDirect() async {
    setState(() => status = 'Ricerca WitMotion…');
    try {
      final found = <BluetoothDevice>[];
      final sub = FlutterBluePlus.scanResults.listen((rs) {
        for (final r in rs) {
          final isWt = r.device.platformName.toUpperCase().startsWith('WT') ||
              r.advertisementData.serviceUuids.contains(kWtSvc);
          if (isWt && !found.any((d) => d.remoteId == r.device.remoteId)) found.add(r.device);
        }
      });
      await FlutterBluePlus.startScan(timeout: const Duration(seconds: 8));
      await FlutterBluePlus.isScanning.where((s) => s == false).first;
      await sub.cancel();
      if (found.isEmpty) {
        setState(() => status = 'Nessun WitMotion trovato');
        return;
      }
      for (int i = 0; i < found.length && i < 2; i++) {
        await attachWt(i, found[i]);
      }
      directMode = true;
      directTimer?.cancel();
      directTimer = Timer.periodic(const Duration(milliseconds: 100), (_) {
        if (!directMode) return;
        buf.add(List<double>.from(last));
        if (buf.length > kMax) buf.removeAt(0);
      });
      setState(() => status = 'WitMotion collegati: ${found.length > 2 ? 2 : found.length}');
    } catch (e) {
      setState(() => status = 'Errore: $e');
    }
  }

  Future<void> attachWt(int i, BluetoothDevice d) async {
    await d.connect();
    d.connectionState.listen((st) {
      if (st == BluetoothConnectionState.disconnected && mounted) setState(() => wtLive[i] = false);
    });
    final services = await d.discoverServices();
      for (final sv in services) {
      for (final c in sv.characteristics) {
        if (sv.uuid == kWtSvc && c.properties.notify) {
          await c.setNotifyValue(true);
          d.cancelWhenDisconnected(c.onValueReceived.listen((v) => onWt(i, v)));
        }
        if (sv.uuid == kBatSvc && c.uuid == kBatChr) {
          if (c.properties.read) {
            final val = await c.read();
            if (val.isNotEmpty && mounted) setState(() => wtBat[i] = val.first);
          }
          if (c.properties.notify) {
            await c.setNotifyValue(true);
            d.cancelWhenDisconnected(c.onValueReceived.listen((val) {
              if (val.isNotEmpty && mounted) setState(() => wtBat[i] = val.first);
            }));
          }
        }
      }
    }

    wtDev[i] = d;
    wtLive[i] = true;
  }

  int s16(int lo, int hi) => ((hi << 8) | lo).toSigned(16);

  // Pacchetti WitMotion: 0x55 0x61 (20 byte: acc, giro, angoli) oppure 0x55 0x51/0x52/0x53 (11 byte)
  void onWt(int i, List<int> v) {
    wtRaw[i] = v.map((b) => b.toRadixString(16).padLeft(2, '0')).join(' ');
    final b = wtBuf[i];
    b.addAll(v);
    final base = i == 0 ? 17 : 26;
    while (b.length >= 2) {
      if (b[0] != 0x55) {
        b.removeAt(0);
        continue;
      }
      final f = b[1];
      final need = f == 0x61 ? 20 : 11;
      if (b.length < need) break;
      final fr = List<int>.from(b.sublist(0, need));
      b.removeRange(0, need);
      if (f == 0x61) {
        for (int k = 0; k < 3; k++) {
          last[base + k] = s16(fr[2 + 2 * k], fr[3 + 2 * k]) / 32768.0 * 16;
          last[base + 3 + k] = s16(fr[8 + 2 * k], fr[9 + 2 * k]) / 32768.0 * 2000;
          last[base + 6 + k] = s16(fr[14 + 2 * k], fr[15 + 2 * k]) / 32768.0 * 180;
        }
        wtCount[i]++;
      } else if (f == 0x51 || f == 0x52 || f == 0x53) {
        final scale = f == 0x51 ? 16.0 : f == 0x52 ? 2000.0 : 180.0;
        final off = f == 0x51 ? 0 : f == 0x52 ? 3 : 6;
        for (int k = 0; k < 3; k++) {
          last[base + off + k] = s16(fr[2 + 2 * k], fr[3 + 2 * k]) / 32768.0 * scale;
        }
        wtCount[i]++;
      }
    }
  }

  void onPkt(List<int> d) {
    if (d.isEmpty) return;
    final q = d[0];
    if (q == 0) got = 0;
    if (q * 19 != got) return;
    for (int i = 1; i < d.length && got < kLen; i++) {
      asm[got++] = d[i];
    }
    if (got >= kLen) parse();
  }

  void parse() {
    final bd = ByteData.sublistView(asm);
    final v = <double>[];
    for (int i = 0; i < 35; i++) {
      v.add(bd.getFloat32(4 + i * 4, Endian.little));
    }
    final ab = 44330.0 * (1 - math.pow(v[10] / 1013.25, 0.1903));
    alt0 ??= ab;
    lastAbs = ab;
    v.add(ab);
    flags = asm[144];
    flags2 = asm[145];
    if ((flags & 8) != 0 && (prevFlags & 8) == 0) shocks++;
    prevFlags = flags;
    buf.add(v);
    if (buf.length > kMax) buf.removeAt(0);
    last = v;
    if (recOn) {
      final t = bd.getUint32(0, Endian.little);
      final row = <String>[t.toString()];
      for (int i = 0; i < 35; i++) {
        row.add(v[i].toStringAsFixed(3));
      }
      row.add((ab - alt0!).toStringAsFixed(2));
      rec.add(row.join(','));
    }
  }

  Future<void> tx(List<int> b) async {
    try {
      await cmdC?.write(b);
    } catch (e) {
      setState(() => status = 'Errore comando: $e');
    }
  }

  void onFile(List<int> d) {
    if (d.length == 1 && d[0] == 4) {
      endFile();
      return;
    }
    fbytes.addAll(d);
    if (fmode == 'file') setState(() => fprog = '$fcur: ${fbytes.length} byte');
  }

  Future<void> endFile() async {
    final txt = utf8.decode(fbytes, allowMalformed: true);
    final m = fmode;
    fmode = '';
    if (m == 'list') {
      final rows = txt.trim().split('\n').where((l) => l.isNotEmpty).map((l) => l.split(',')).toList();
      setState(() => files = rows);
    } else if (m == 'file') {
      await saveShare(fcur, txt);
      setState(() => fprog = '$fcur: salvato');
    }
  }

  Future<void> saveShare(String name, String text) async {
    final dir = await getTemporaryDirectory();
    final f = File('${dir.path}/$name');
    await f.writeAsString(text);
    await Share.shareXFiles([XFile(f.path)]);
  }

  Future<void> setClock() async {
    final now = DateTime.now();
    final e = now.millisecondsSinceEpoch ~/ 1000 + now.timeZoneOffset.inSeconds;
    await tx([4, e & 255, (e >> 8) & 255, (e >> 16) & 255, (e >> 24) & 255]);
  }

  Future<void> toggleRecPhone() async {
    if (!recOn) {
      rec.clear();
      setState(() => recOn = true);
    } else {
      setState(() => recOn = false);
      if (rec.isNotEmpty) {
        final ts = DateTime.now().millisecondsSinceEpoch;
        await saveShare('sessione_$ts.csv', '$kHdr\n${rec.join('\n')}');
      }
    }
  }

  // ---------- interfaccia ----------
  List<List<double>> windowData() {
    final n = windowSec * 10;
    return buf.length <= n ? buf : buf.sublist(buf.length - n);
  }

  Widget metric(String label, String value) {
    return Card(
      child: Padding(
        padding: const EdgeInsets.all(10),
        child: Column(crossAxisAlignment: CrossAxisAlignment.start, children: [
          Text(label, style: Theme.of(context).textTheme.bodySmall),
          const SizedBox(height: 2),
          Text(value, style: Theme.of(context).textTheme.titleMedium),
        ]),
      ),
    );
  }

  Widget grid(List<Widget> items) {
    return GridView.count(
      crossAxisCount: 2,
      shrinkWrap: true,
      physics: const NeverScrollableScrollPhysics(),
      childAspectRatio: 2.4,
      children: items,
    );
  }

  Widget chart(ChartDef d) {
    final off = d.rel ? (alt0 ?? 0) : 0.0;
    final spans = <TextSpan>[];
    for (int j = 0; j < d.idx.length; j++) {
      spans.add(TextSpan(
        text: '${d.names[j]} ${(last[d.idx[j]] - off).toStringAsFixed(d.dp)}  ',
        style: TextStyle(color: LinePainter.cols[d.idx.length > 1 ? j : 2], fontSize: 12),
      ));
    }
    return Card(
      child: Padding(
        padding: const EdgeInsets.all(10),
        child: Column(crossAxisAlignment: CrossAxisAlignment.start, children: [
          Text(d.title, style: Theme.of(context).textTheme.bodySmall),
          Text.rich(TextSpan(children: spans)),
          const SizedBox(height: 4),
          SizedBox(
            height: 110,
            child: CustomPaint(
              size: Size.infinite,
              painter: LinePainter(windowData(), d.idx, off, Theme.of(context).colorScheme.outline,
                  Theme.of(context).colorScheme.onSurfaceVariant),
            ),
          ),
        ]),
      ),
    );
  }

  Widget windowBar() {
    return Row(children: [
      const Text('Finestra: '),
      DropdownButton<int>(
        value: windowSec,
        items: const [10, 30, 60, 120, 180]
            .map((s) => DropdownMenuItem(value: s, child: Text('$s s')))
            .toList(),
        onChanged: (v) => setState(() => windowSec = v ?? 30),
      ),
      const Spacer(),
      TextButton(onPressed: () => setState(() => alt0 = lastAbs), child: const Text('Azzera quota')),
    ]);
  }

  Widget sensorTab() {
    final sdOk = (flags & 4) != 0;
    final logging = (flags & 1) != 0;
    final bv = last[15];
    final batt = bv < 1 ? 'non misurata' : '${batPct(bv)}% (${bv.toStringAsFixed(2)} V)';
    return ListView(padding: const EdgeInsets.all(12), children: [
      if (shocks > 0) Card(color: Colors.red.shade700, child: ListTile(title: Text('Urti rilevati: $shocks', style: const TextStyle(color: Colors.white)), trailing: TextButton(onPressed: () => setState(() => shocks = 0), child: const Text('Azzera', style: TextStyle(color: Colors.white))))),
      if ((flags & 32) != 0) const Card(child: ListTile(title: Text('Batteria scarica: ricarica il sensore'))),
      grid([
        metric('Temperatura', '${last[9].toStringAsFixed(1)} °C'),
        metric('Pressione', '${last[10].toStringAsFixed(1)} hPa'),
        metric('Batteria', batt),
        metric('Quota relativa', '${(last[35] - (alt0 ?? 0)).toStringAsFixed(1)} m'),
      ]),
      Card(
        child: Padding(
          padding: const EdgeInsets.all(10),
          child: Column(crossAxisAlignment: CrossAxisAlignment.start, children: [
            const Text('Registrazione su microSD'),
            Text(!sdOk ? 'microSD non rilevata' : logging ? 'In registrazione' : 'Ferma',
                style: TextStyle(fontWeight: FontWeight.w500, color: logging ? Colors.red : null)),
            Row(children: [
              FilledButton.tonal(onPressed: connected && sdOk && !logging ? () => tx([1]) : null, child: const Text('Avvia')),
              const SizedBox(width: 8),
              FilledButton.tonal(onPressed: connected && logging ? () => tx([0]) : null, child: const Text('Ferma')),
              const Spacer(),
              const Text('Auto'),
              Switch(value: (flags & 2) != 0, onChanged: connected ? (v) => tx([v ? 2 : 3]) : null),
            ]),
            const Text('Il pulsante BOOT o il touch sul sensore avviano e fermano la registrazione anche senza telefono.',
                style: TextStyle(fontSize: 12)),
          ]),
        ),
      ),
      windowBar(),
      for (final d in sensorCharts) chart(d),
    ]);
  }

  Widget wtTab(int n) {
    final on = directMode ? wtLive[n - 1] : (n == 1 ? (flags & 128) != 0 : (flags2 & 1) != 0);
    final b = n == 1 ? 17 : 26;
    String f(int i, int dp) => last[b + i].toStringAsFixed(dp);
    return ListView(padding: const EdgeInsets.all(12), children: [
      ListTile(
        title: Text('WT9011DCL $n'),
        subtitle: directMode
            ? Text('Batteria: ${wtBat[n - 1] != null ? '${wtBat[n - 1]}%' : 'non disponibile'}')
            : null,
        trailing: Text(on ? 'connesso' : 'non connesso', style: TextStyle(color: on ? Colors.green : Colors.red)),
      ),

      if (directMode)
        Text('Frame ricevuti: ${wtCount[n - 1]}  ultimo pacchetto: ${wtRaw[n - 1]}', style: const TextStyle(fontSize: 11)),
      grid([
        metric('Acc X (g)', f(0, 2)), metric('Acc Y (g)', f(1, 2)), metric('Acc Z (g)', f(2, 2)),
        metric('Giro X (°/s)', f(3, 1)), metric('Giro Y (°/s)', f(4, 1)), metric('Giro Z (°/s)', f(5, 1)),
        metric('Roll (°)', f(6, 1)), metric('Pitch (°)', f(7, 1)), metric('Yaw (°)', f(8, 1)),
      ]),
      windowBar(),
      for (final d in wtCharts(n)) chart(d),
    ]);
  }

  Widget toolsTab() {
    return ListView(padding: const EdgeInsets.all(12), children: [
      const Text('Orologio e calibrazione'),
      Wrap(spacing: 8, children: [
        OutlinedButton(onPressed: connected ? setClock : null, child: const Text('Imposta orologio')),
        OutlinedButton(onPressed: connected ? () => tx([5]) : null, child: const Text('Calibra accel/giro')),
        OutlinedButton(onPressed: connected ? () => tx([6]) : null, child: const Text('Calibra magnetometro')),
        OutlinedButton(onPressed: connected ? () => tx([11]) : null, child: const Text('Dimentica sensori WT')),
      ]),
      const Text('Accel/giro: sensore fermo e in piano. Magnetometro: ruotalo per 15 s.', style: TextStyle(fontSize: 12)),
      (flags & 64) != 0 ? const Text('Calibrazione in corso…') : const SizedBox.shrink(),
      const Divider(),
      const Text('Parametri del sensore'),
      Row(children: [
        DropdownButton<int>(
          value: rng,
          items: const [0, 1, 2, 3].map((i) => DropdownMenuItem(value: i, child: Text('±${[2, 4, 8, 16][i]} g'))).toList(),
          onChanged: (v) => setState(() => rng = v ?? 3),
        ),
        const SizedBox(width: 16),
        DropdownButton<int>(
          value: rate,
          items: const [100, 200, 500, 1000].map((r) => DropdownMenuItem(value: r, child: Text('$r Hz'))).toList(),
          onChanged: (v) => setState(() => rate = v ?? 200),
        ),
      ]),
      Text('Soglia urto: ${shock.toStringAsFixed(1)} g'),
      Slider(value: shock, min: 1, max: 25, divisions: 48, onChanged: (v) => setState(() => shock = v)),
      OutlinedButton(
        onPressed: connected
            ? () {
                tx([10, rng, rate & 255, rate >> 8, (shock * 10).round()]);
                setState(() => status = 'Parametri salvati: il sensore si riavvia, riconnettiti');
              }
            : null,
        child: const Text('Salva e riavvia sensore'),
      ),
      const Divider(),
      const Text('File sulla microSD'),
      OutlinedButton(
        onPressed: connected && (flags & 1) == 0
            ? () {
                fmode = 'list';
                fbytes.clear();
                tx([7]);
              }
            : null,
        child: const Text('Leggi elenco'),
      ),
      for (final r in files)
        ListTile(
          dense: true,
          title: Text(r[0]),
          subtitle: Text(r.length > 1 ? '${(int.tryParse(r[1]) ?? 0) ~/ 1024} KB' : ''),
          trailing: TextButton(
            child: const Text('Scarica'),
            onPressed: () {
              fmode = 'file';
              fcur = r[0];
              fbytes.clear();
              setState(() => fprog = '$fcur: 0 byte');
              tx([8, ...r[0].codeUnits]);
            },
          ),
        ),
      Text(fprog),
      const Text('Il Bluetooth è lento: adatto a file brevi.', style: TextStyle(fontSize: 12)),
      const Divider(),
      const Text('Registrazione sul telefono (10 campioni/s)'),
      Row(children: [
        FilledButton.tonal(onPressed: connected ? toggleRecPhone : null, child: Text(recOn ? 'Ferma e condividi' : 'Avvia')),
        const SizedBox(width: 12),
        Text('${rec.length} campioni'),
      ]),
    ]);
  }

  @override
  Widget build(BuildContext context) {
    return DefaultTabController(
      length: 4,
      child: Scaffold(
        appBar: AppBar(
          title: const Text('Datalogger 9 assi'),
          actions: [
            TextButton(
              onPressed: (connected || directMode) ? null : connectWtDirect,
              child: const Text('WT diretto'),
            ),
            TextButton(
              onPressed: (connected || directMode) ? disconnectDev : connectDev,
              child: Text((connected || directMode) ? 'Disconnetti' : 'Connetti'),
            ),
          ],
          bottom: const TabBar(tabs: [
            Tab(text: 'Sensore'), Tab(text: 'WT1'), Tab(text: 'WT2'), Tab(text: 'Strumenti'),
          ]),
        ),
        body: Column(children: [
          Container(
            width: double.infinity,
            padding: const EdgeInsets.symmetric(vertical: 4, horizontal: 12),
            child: Text(status, style: TextStyle(color: connected ? Colors.green : null)),
          ),
          Expanded(child: TabBarView(children: [sensorTab(), wtTab(1), wtTab(2), toolsTab()])),
        ]),
      ),
    );
  }
}

class LinePainter extends CustomPainter {
  final List<List<double>> data;
  final List<int> idx;
  final double off;
  final Color grid;
  final Color textColor;
  static const List<Color> cols = [Color(0xFFE5484D), Color(0xFF30A46C), Color(0xFF3E63DD)];

  LinePainter(this.data, this.idx, this.off, this.grid, this.textColor);

  @override
  void paint(Canvas c, Size s) {
    final border = Paint()
      ..style = PaintingStyle.stroke
      ..color = grid
      ..strokeWidth = 0.5;
    c.drawRect(Offset.zero & s, border);
    if (data.length < 2) return;
    double lo = double.infinity, hi = -double.infinity;
    for (final r in data) {
      for (final k in idx) {
        final v = r[k] - off;
        lo = math.min(lo, v);
        hi = math.max(hi, v);
      }
    }
    if (hi - lo < 1e-6) {
      hi += 0.5;
      lo -= 0.5;
    }
    final pad = (hi - lo) * 0.1;
    lo -= pad;
    hi += pad;
    for (int j = 0; j < idx.length; j++) {
      final p = Paint()
        ..style = PaintingStyle.stroke
        ..strokeWidth = 1.6
        ..color = cols[idx.length > 1 ? j : 2];
      final path = Path();
      for (int i = 0; i < data.length; i++) {
        final x = s.width * (i / (data.length - 1));
        final y = s.height - (data[i][idx[j]] - off - lo) / (hi - lo) * s.height;
        if (i == 0) {
          path.moveTo(x, y);
        } else {
          path.lineTo(x, y);
        }
      }
      c.drawPath(path, p);
    }
    label(c, hi.toStringAsFixed(1), const Offset(3, 2));
    label(c, lo.toStringAsFixed(1), Offset(3, s.height - 14));
  }

  void label(Canvas c, String t, Offset o) {
    final tp = TextPainter(
      text: TextSpan(text: t, style: TextStyle(fontSize: 10, color: textColor)),
      textDirection: TextDirection.ltr,
    )..layout();
    tp.paint(c, o);
  }

  @override
  bool shouldRepaint(covariant LinePainter old) => true;
}
