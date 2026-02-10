// lib/kiaro_cipher.dart
//
// KiaroCipher: cifratura/decifratura basata su:
// - mappa lessicale "whole word" (encryptMap / decryptMap)
// - morfologia (form -> lemma+tag, lemma+tag -> form)
// - gestione elisioni fisse (l', un', ...)
// - split clitici (lasciate + mi, ecc.)
// - permutazione deterministica dei verbi (infinito -> infinito) per coniugazione
//
// STEP 2 FIX:
// - in DECRYPT la permutazione verbi deve andare SEMPRE all’indietro (mappa inversa).
// - costruzione mapping verbi: niente putIfAbsent (evita inverse-map “sporca”).
// - fallback safety: se manca l’inversa, ricava l’inverso dalla forward-map.
//
// STEP 3 FIX (whole-word decrypt robusto):
// - se decryptMap contiene mapping identità (es. "telecamere" -> "telecamere"),
// NON deve bloccare il fallback inverso da encryptMap.
//
// STEP 4 FIX (telecamere):
// - costruzione _encryptInverseWholeWord a DUE PASSI:
//   1) prima inserisce SOLO mapping non-identità (plain != cipher)
//   2) poi inserisce le identità SOLO se quel cipher non esiste già
//   => un’identità non può più “vincere” contro un mapping reale.
class KiaroCipher {
  final Map<String, String> _encryptMap; // plain -> cipher
  final Map<String, String> _decryptMap; // cipher -> plain

  // Inversa “di sicurezza” della encryptMap (cipher -> plain).
  // Nota: se più plain mappano allo stesso cipher, si tiene la prima voce incontrata
  // (deterministico in Dart perché l’ordine d’inserimento delle Map è stabile).
  final Map<String, String> _encryptInverseWholeWord = {};

  final Set<String> _clitics;
  final Set<String> _verbInfinitives = {};
  final int _debugTruncate;

  // MORFOLOGIA
  final Map<String, List<Map<String, String>>>
      _formToLemmaTags; // form -> [{lemma, tag}]
  final Map<String, Map<String, String>>
      _lemmaTagToForm; // lemma -> {tag: form}

  // Elisioni fisse: NON cambiare UI/format, solo parsing testuale.
  static const Set<String> _fixedElisionPrefixes = {
    "l'",
    "un'",
    "d'",
    "all'",
    "dall'",
    "dell'",
    "nell'",
    "sull'",
    "coll'",
    "pell'",
    "gliel'",
    "m'",
    "t'",
    "s'",
    "c'",
    "v'",
  };

  // Se true, richiede che la parola cifrata dopo elisione inizi con vocale o 'h'
  static const bool _strictElisionVowelOrH = false;

  // Infiniti tronchi ammessi (stile poetico): far, dar, dir, star, ...
  static const Set<String> _allowedTruncatedInfinitives = {
    'far',
    'dar',
    'dir',
    'star',
    'andar',
    'esser',
    'aver',
    'venir',
    'tener',
    'poter',
    'voler',
    'saper',
  };

  // Irregolari “noti”: li separiamo solo se presenti in lemmaTagToForm (per coniugazioni)
  static const Set<String> _knownIrregularInfinitives = {
    'essere',
    'avere',
    'fare',
    'dare',
    'dire',
    'stare',
    'andare',
    'venire',
    'tenere',
    'potere',
    'volere',
    'sapere',
    'dovere',
  };

  // Permutazione verbi (infinito -> infinito), invertibile
  final Map<String, String> _verbPlainInfToCipherInf = {}; // forward
  final Map<String, String> _verbCipherInfToPlainInf = {}; // inverse

  KiaroCipher({
    required Map<String, String> encryptMap,
    required Map<String, String> decryptMap,
    Set<String>? clitics,
    int debugTruncate = 120,
    Map<String, List<Map<String, String>>>? formToLemmaTags,
    Map<String, Map<String, String>>? lemmaTagToForm,
  })  : _encryptMap = _normalizeStringMapKeys(encryptMap),
        _decryptMap = _normalizeStringMapKeys(decryptMap),
        _clitics = (clitics ??
                {
                  'mi',
                  'ti',
                  'si',
                  'ci',
                  'vi',
                  'ne',
                  'lo',
                  'la',
                  'li',
                  'le',
                  'gli',
                  'glie',
                  'melo',
                  'mela',
                  'meli',
                  'mele',
                  'telo',
                  'tela',
                  'teli',
                  'tele',
                  'selo',
                  'sela',
                  'seli',
                  'sele',
                  'celo',
                  'cela',
                  'celi',
                  'cele',
                  'velo',
                  'vela',
                  'veli',
                  'vele',
                  'glielo',
                  'gliela',
                  'glieli',
                  'gliele',
                })
            .map(_normalizeKey)
            .toSet(),
        _debugTruncate = debugTruncate,
        _formToLemmaTags =
            _normalizeFormToLemmaTags(formToLemmaTags ?? const {}),
        _lemmaTagToForm = _normalizeLemmaTagToForm(lemmaTagToForm ?? const {}) {
    _buildEncryptInverseWholeWord();
    _buildVerbPermutationIndices();
  }

  // =========================
  // API PUBBLICA
  // =========================

  String encrypt(String text) {
    if (text.isEmpty) return text;
    text = text.replaceAll('’', "'");
    // FIX: rimuovi invisibili/bidi PRIMA della tokenizzazione (keep-case)
    text = _stripInvisiblesKeepCase(text);

    final sb = StringBuffer();
    var i = 0;

    while (i < text.length) {
      final fixedPrefix = _tryReadFixedElisionPrefix(text, i);
      if (fixedPrefix != null) {
        sb.write(fixedPrefix);
        i += fixedPrefix.length;

        final wordStart = i;
        while (i < text.length && _isLetter(text[i])) {
          i++;
        }
        final rawWord = text.substring(wordStart, i);
        if (rawWord.isEmpty) continue;

        final encWord = _encryptWord(rawWord);
        if (_strictElisionVowelOrH) {
          final lowerEnc = encWord.toLowerCase();
          if (!_startsWithVowelOrH(lowerEnc)) {
            _dPrint(
                'encrypt', 'Elision check failed for "$rawWord" -> "$encWord"');
            sb.write(rawWord);
          } else {
            sb.write(encWord);
          }
        } else {
          sb.write(encWord);
        }
        continue;
      }

      final ch = text[i];
      if (_isLetter(ch)) {
        final start = i;
        while (i < text.length && _isLetter(text[i])) {
          i++;
        }
        final word = text.substring(start, i);
        sb.write(_encryptWord(word));
        continue;
      }

      sb.write(ch);
      i++;
    }

    return sb.toString();
  }

  String decrypt(String text) {
    if (text.isEmpty) return text;
    text = text.replaceAll('’', "'");
    // FIX: rimuovi invisibili/bidi PRIMA della tokenizzazione (keep-case)
    text = _stripInvisiblesKeepCase(text);

    final sb = StringBuffer();
    var i = 0;
    while (i < text.length) {
      final fixedPrefix = _tryReadFixedElisionPrefix(text, i);
      if (fixedPrefix != null) {
        sb.write(fixedPrefix);
        i += fixedPrefix.length;

        final wordStart = i;
        while (i < text.length && _isLetter(text[i])) {
          i++;
        }

        final rawWord = text.substring(wordStart, i);
        if (rawWord.isEmpty) continue;

        sb.write(_decryptWord(rawWord));
        continue;
      }

      final ch = text[i];
      if (_isLetter(ch)) {
        final start = i;
        while (i < text.length && _isLetter(text[i])) {
          i++;
        }
        final word = text.substring(start, i);
        sb.write(_decryptWord(word));
        continue;
      }

      sb.write(ch);
      i++;
    }

    return sb.toString();
  }

  String encryptTimes(String text, [int times = 1]) {
    var out = text;
    final n = times < 1 ? 1 : times;
    for (var i = 0; i < n; i++) {
      out = encrypt(out);
    }
    return out;
  }

  String decryptTimes(String text, [int times = 1]) {
    var out = text;
    final n = times < 1 ? 1 : times;
    for (var i = 0; i < n; i++) {
      out = decrypt(out);
    }
    return out;
  }

  // =========================
  // WORD-LEVEL
  // =========================

  String _encryptWord(String original) {
    if (original.isEmpty) return original;

    final key = _normalizeKey(original);

    // A) Se è forma verbale riconosciuta: pipeline verbo->verbo->flessione
    final verbFirst = _mapByLemmaAndTagPreferVerbs(key, encrypt: true);
    if (verbFirst != null && verbFirst != key) {
      return _adjustCaseLike(original, verbFirst);
    }

    // B) Se è un infinito: forza infinito->infinito (mai mapping diretto “a caso”)
    if (_isInfinitive(key)) {
      final mapped = _mapVerbLemmaForTag(key, 'VER:infi', encrypt: true) ?? key;
      if (mapped != key) {
        _dPrint('_encryptWord', 'Verb INFI forced "$key" -> "$mapped"');
      }
      return _adjustCaseLike(original, mapped);
    }

    // C) Mapping diretto (WHOLE word)
    final directWhole = _encryptMap[key];
    if (directWhole != null && directWhole != key) {
      _dPrint('_encryptWord', 'Direct WHOLE map "$key" -> "$directWhole"');
      return _adjustCaseLike(original, directWhole);
    }

    // D) Morfologia non-verbale
    final morphMapped = _mapByLemmaAndTag(key, encrypt: true, verbsAlso: false);
    if (morphMapped != null && morphMapped != key) {
      _dPrint('_encryptWord', 'Morph-based map "$key" -> "$morphMapped"');
      return _adjustCaseLike(original, morphMapped);
    }

    // E) Split clitico + mapping sul lemma
    final split = _splitClitic(key);
    final lemmaLower = split.lemma ?? key;
    final cliticLower = split.clitic;
    if (cliticLower == null) {
      return _adjustCaseLike(original, lemmaLower);
    }

    final prep = _prepareLemmaForLookup(lemmaLower);
    final lookupLemma = prep.lookup;

    var mapped = false;
    String encryptedLemmaLower = lookupLemma;

    if (_isInfinitive(lookupLemma)) {
      encryptedLemmaLower =
          _mapVerbLemmaForTag(lookupLemma, 'VER:infi', encrypt: true) ??
              lookupLemma;
      mapped = encryptedLemmaLower != lookupLemma;
    } else {
      final directLemma = _encryptMap[lookupLemma];
      if (directLemma != null && directLemma != lookupLemma) {
        encryptedLemmaLower = directLemma;
        mapped = true;
      } else {
        final mm =
            _mapByLemmaAndTag(lookupLemma, encrypt: true, verbsAlso: false);
        if (mm != null && mm != lookupLemma) {
          encryptedLemmaLower = mm;
          mapped = true;
        }
      }
    }

    var baseOut = encryptedLemmaLower;
    if (prep.truncatedInfinitive && !mapped) baseOut = prep.original;
    if (prep.truncatedInfinitive && mapped) {
      baseOut = _maybeRetruncateInfinitive(baseOut);
    }

    final combinedLower = baseOut + cliticLower;
    return _adjustCaseLike(original, combinedLower);
  }

  String _decryptWord(String original) {
    if (original.isEmpty) return original;

    final key = _normalizeKey(original);

    // A) Se è forma verbale riconosciuta: pipeline verbo->verbo->flessione
    final verbFirst = _mapByLemmaAndTagPreferVerbs(key, encrypt: false);
    if (verbFirst != null && verbFirst != key) {
      return _adjustCaseLike(original, verbFirst);
    }

    // B) Se è un infinito: forza infinito->infinito
    if (_isInfinitive(key)) {
      final mapped =
          _mapVerbLemmaForTag(key, 'VER:infi', encrypt: false) ?? key;
      if (mapped != key) {
        _dPrint('_decryptWord', 'Verb INFI forced "$key" -> "$mapped"');
      }
      return _adjustCaseLike(original, mapped);
    }

    // C) Mapping diretto (WHOLE word) + fallback inverso encryptMap
    final directWhole = _decryptWholeWord(key);
    if (directWhole != null && directWhole != key) {
      _dPrint('_decryptWord', 'Direct WHOLE map "$key" -> "$directWhole"');
      return _adjustCaseLike(original, directWhole);
    }

    // D) Morfologia non-verbale
    final morphMapped =
        _mapByLemmaAndTag(key, encrypt: false, verbsAlso: false);
    if (morphMapped != null && morphMapped != key) {
      _dPrint('_decryptWord', 'Morph-based map "$key" -> "$morphMapped"');
      return _adjustCaseLike(original, morphMapped);
    }

    // E) Split clitico + mapping sul lemma
    final split = _splitClitic(key);
    final lemmaLower = split.lemma ?? key;
    final cliticLower = split.clitic;
    if (cliticLower == null) {
      return _adjustCaseLike(original, lemmaLower);
    }

    final prep = _prepareLemmaForLookup(lemmaLower);
    final lookupLemma = prep.lookup;

    var mapped = false;
    String decryptedLemmaLower = lookupLemma;

    if (_isInfinitive(lookupLemma)) {
      decryptedLemmaLower =
          _mapVerbLemmaForTag(lookupLemma, 'VER:infi', encrypt: false) ??
              lookupLemma;
      mapped = decryptedLemmaLower != lookupLemma;
    } else {
      final directLemma = _decryptWholeWord(lookupLemma);
      if (directLemma != null && directLemma != lookupLemma) {
        decryptedLemmaLower = directLemma;
        mapped = true;
      } else {
        final mm =
            _mapByLemmaAndTag(lookupLemma, encrypt: false, verbsAlso: false);
        if (mm != null && mm != lookupLemma) {
          decryptedLemmaLower = mm;
          mapped = true;
        }
      }
    }

    var baseOut = decryptedLemmaLower;
    if (prep.truncatedInfinitive && !mapped) baseOut = prep.original;
    if (prep.truncatedInfinitive && mapped) {
      baseOut = _maybeRetruncateInfinitive(baseOut);
    }

    final combinedLower = baseOut + cliticLower;
    return _adjustCaseLike(original, combinedLower);
  }

  // =========================
  // WHOLE WORD HELPERS (DECRYPT)
  // =========================

  void _buildEncryptInverseWholeWord() {
    _encryptInverseWholeWord.clear();

    // PASS 1: inserisci SOLO mapping non-identità (prioritari)
    for (final e in _encryptMap.entries) {
      final plain = _normalizeKey(e.key);
      final cipher = _normalizeKey(e.value);

      if (cipher.isEmpty) continue;
      if (plain == cipher) continue;

      final existing = _encryptInverseWholeWord[cipher];
      if (existing == null) {
        _encryptInverseWholeWord[cipher] = plain;
      } else if (existing != plain) {
        _dPrint(
          '_buildEncryptInverseWholeWord',
          'WARNING: collision inverse for "$cipher": keeping "$existing", ignoring "$plain"',
        );
      }
    }

    // PASS 2: inserisci le identità SOLO se quel cipher non è già coperto
    for (final e in _encryptMap.entries) {
      final plain = _normalizeKey(e.key);
      final cipher = _normalizeKey(e.value);

      if (cipher.isEmpty) continue;
      if (plain != cipher) continue;

      _encryptInverseWholeWord.putIfAbsent(cipher, () => plain);
    }
  }

  /// Decrypt robusto:
  /// - usa decryptMap se produce un risultato *diverso* dalla chiave
  /// - altrimenti prova l’inversa di encryptMap (fallback)
  String? _decryptWholeWord(String cipherLowerKey) {
    final k = _normalizeKey(cipherLowerKey);
    final direct = _decryptMap[k];

    // FIX: se direct è mapping-identità, NON bloccare il fallback.
    if (direct != null && direct != k) return direct;

    if (direct != null && direct == k) {
      _dPrint('_decryptWholeWord',
          'Direct decryptMap identity "$k" -> "$direct" (ignored, trying fallback)');
    }

    final fallback = _encryptInverseWholeWord[k];
    if (fallback != null && fallback != k) {
      _dPrint('_decryptWholeWord',
          'Fallback inverse encryptMap "$k" -> "$fallback"');
      return fallback;
    }

    return direct; // se esiste ma è identità, torna identità; altrimenti null
  }

  // =========================
  // MORFOLOGIA (lemma + tag)
  // =========================

  String? _mapByLemmaAndTagPreferVerbs(
    String lowerWordKey, {
    required bool encrypt,
  }) {
    final analyses = _formToLemmaTags[lowerWordKey];
    if (analyses == null || analyses.isEmpty) return null;

    // 1) Prova SOLO analisi verbali, in ordine
    for (final a in analyses) {
      final lemma = a['lemma'];
      final tag = (a['tag'] ?? a['tags'])?.trim();

      if (lemma == null || tag == null || tag.isEmpty) continue;
      if (!tag.startsWith('VER:')) continue;

      final lemmaLower = _normalizeKey(lemma);
      if (!_isInfinitive(lemmaLower)) continue;

      final mappedVerbLemma =
          _mapVerbLemmaForTag(lemmaLower, tag, encrypt: encrypt) ?? lemmaLower;

      // dizionario
      final formsByTag = _lemmaTagToForm[mappedVerbLemma];
      final outDict = formsByTag != null ? formsByTag[tag] : null;
      if (outDict != null && outDict.isNotEmpty) {
        _dPrint(
          '_mapByLemmaAndTag',
          'VER "$lowerWordKey" ($lemmaLower,$tag) -> "$outDict" via dict (mappedLemma="$mappedVerbLemma")',
        );
        return outDict;
      }

      // regole
      final outReg = _inflectRegularVerbByTag(mappedVerbLemma, tag);
      if (outReg != null && outReg.isNotEmpty) {
        _dPrint(
          '_mapByLemmaAndTag',
          'VER "$lowerWordKey" ($lemmaLower,$tag) -> "$outReg" via rules (mappedLemma="$mappedVerbLemma")',
        );
        return outReg;
      }

      _dPrint(
        '_mapByLemmaAndTag',
        'VER "$lowerWordKey" ($lemmaLower,$tag) fallback -> "$mappedVerbLemma"',
      );
      return mappedVerbLemma;
    }

    // 2) Se non ho trovato nessuna analisi VER utilizzabile, non forzo nulla
    return null;
  }

  /// Mapping morfologico "forma" -> "lemma+tag" -> "forma" (in output).
  ///
  /// - Se `verbsAlso` è false: ignora completamente i VER (i verbi li gestisci altrove).
  /// - Se `verbsAlso` è true: può gestire anche VER, ma **non forza** fallback a lemma
  /// (tranne i casi gestiti da `_mapByLemmaAndTagPreferVerbs`).
  String? _mapByLemmaAndTag(
    String lowerWordKey, {
    required bool encrypt,
    required bool verbsAlso,
  }) {
    final key = _normalizeKey(lowerWordKey);
    final analyses = _formToLemmaTags[key];
    if (analyses == null || analyses.isEmpty) return null;

    for (final a in analyses) {
      final lemma = a['lemma'];
      final tag = (a['tag'] ?? a['tags'])?.trim();

      if (lemma == null || tag == null || tag.isEmpty) continue;

      final isVerb = tag.startsWith('VER:');
      if (isVerb && !verbsAlso) continue;

      final lemmaLower = _normalizeKey(lemma);

      // 1) Mappa lemma -> lemma (cipher/plain) in base al tipo
      String mappedLemma = lemmaLower;

      if (isVerb && _isInfinitive(lemmaLower)) {
        mappedLemma = _mapVerbLemmaForTag(lemmaLower, tag, encrypt: encrypt) ??
            lemmaLower;
      } else {
        if (encrypt) {
          final directLemma = _encryptMap[lemmaLower];
          if (directLemma != null && directLemma.isNotEmpty) {
            mappedLemma = _normalizeKey(directLemma);
          }
        } else {
          // decrypt: prova decryptMap, poi fallback inverso encryptMap
          final directLemma = _decryptWholeWord(lemmaLower);
          if (directLemma != null && directLemma.isNotEmpty) {
            mappedLemma = _normalizeKey(directLemma);
          }
        }
      }

      // 2) Dizionario lemma+tag -> forma
      final formsByTag = _lemmaTagToForm[mappedLemma];
      final outDict = formsByTag != null ? formsByTag[tag] : null;
      if (outDict != null && outDict.isNotEmpty) {
        return outDict;
      }

      // 3) Regole verbali (se serve)
      if (isVerb && _isInfinitive(mappedLemma)) {
        final outReg = _inflectRegularVerbByTag(mappedLemma, tag);
        if (outReg != null && outReg.isNotEmpty) {
          return outReg;
        }
      }
    }

    return null;
  }

  // =========================
  // VERBI: lemma infinito -> lemma infinito
  // =========================

  String? _mapVerbLemmaForTag(
    String infinitiveLowerKey,
    String tag, {
    required bool encrypt,
  }) {
    final inf = _normalizeKey(infinitiveLowerKey);
    if (!_isInfinitive(inf)) return null;

    // Preferisci mappa lessicale SOLO se infinito->infinito e stessa coniugazione
    final direct = encrypt ? _encryptMap[inf] : _decryptMap[inf];
    if (direct != null) {
      final directKey = _normalizeKey(direct);
      if (_isInfinitive(directKey) &&
          _conjugationOf(directKey) == _conjugationOf(inf)) {
        return directKey;
      }
    }

    return _mapVerbInfinitive(inf, encrypt: encrypt) ?? inf;
  }

  // decrypt deve andare SEMPRE “indietro”.
  // Fallback safety: se manca l’inversa, la ricavo dalla forward-map.
  String? _mapVerbInfinitive(
    String infinitiveLowerKey, {
    required bool encrypt,
  }) {
    final inf = _normalizeKey(infinitiveLowerKey);
    if (!_isInfinitive(inf)) return null;

    if (encrypt) {
      return _verbPlainInfToCipherInf[inf] ?? inf;
    }

    final back = _verbCipherInfToPlainInf[inf];
    if (back != null) return back;

    final recovered = _reverseLookupForwardVerbMap(inf);
    if (recovered != null) return recovered;

    return inf;
  }

  String? _reverseLookupForwardVerbMap(String cipherInf) {
    for (final e in _verbPlainInfToCipherInf.entries) {
      if (e.value == cipherInf) return e.key;
    }
    return null;
  }

  void _buildVerbPermutationIndices() {
    _verbPlainInfToCipherInf.clear();
    _verbCipherInfToPlainInf.clear();

    final verbLemmas = _collectVerbInfinitivesFromMorph();
    _verbInfinitives
      ..clear()
      ..addAll(verbLemmas);

    if (verbLemmas.isEmpty) return;

    final are = <String>[];
    final ere = <String>[];
    final ire = <String>[];
    final irregulars = <String>[];

    for (final inf in verbLemmas) {
      final conj = _conjugationOf(inf);
      if (conj == null) continue;

      if (_knownIrregularInfinitives.contains(inf)) {
        if (_lemmaTagToForm.containsKey(inf)) irregulars.add(inf);
        continue;
      }
      if (conj == 'are') are.add(inf);
      if (conj == 'ere') ere.add(inf);
      if (conj == 'ire') ire.add(inf);
    }

    are.sort();
    ere.sort();
    ire.sort();
    irregulars.sort();

    _fillRotationMapping(are);
    _fillRotationMapping(ere);
    _fillRotationMapping(ire);
    _fillRotationMapping(irregulars);

    _dPrint(
      '_buildVerbPermutationIndices',
      'Verb groups: are=${are.length}, ere=${ere.length}, ire=${ire.length}, irregulars=${irregulars.length}',
    );
  }

  // niente putIfAbsent (evita inverse-map “sporca”)
  void _fillRotationMapping(List<String> group) {
    if (group.length < 2) return;

    for (var i = 0; i < group.length; i++) {
      final a = group[i];
      final b = group[(i + 1) % group.length];

      final oldFwd = _verbPlainInfToCipherInf[a];
      if (oldFwd != null && oldFwd != b) {
        _dPrint('_fillRotationMapping',
            'WARNING: forward verb collision "$a": "$oldFwd" vs "$b"');
      }
      _verbPlainInfToCipherInf[a] = b;

      final oldInv = _verbCipherInfToPlainInf[b];
      if (oldInv != null && oldInv != a) {
        _dPrint('_fillRotationMapping',
            'WARNING: inverse verb collision "$b": "$oldInv" vs "$a"');
      }
      _verbCipherInfToPlainInf[b] = a;
    }
  }

  Set<String> _collectVerbInfinitivesFromMorph() {
    final out = <String>{};

    // 1) dalla mappa forma -> analisi
    _formToLemmaTags.forEach((_, analyses) {
      for (final a in analyses) {
        final lemma = a['lemma'];
        final tag = (a['tag'] ?? a['tags'])?.trim();
        if (lemma == null || tag == null) continue;
        if (!tag.startsWith('VER:')) continue;

        final l = _normalizeKey(lemma);
        if (_conjugationOf(l) != null ||
            _knownIrregularInfinitives.contains(l)) {
          out.add(l);
        }
      }
    });

    // 2) anche dalle chiavi lemma->tag->forma (se sono infiniti)
    for (final lemma in _lemmaTagToForm.keys) {
      final l = _normalizeKey(lemma);
      if (_conjugationOf(l) != null || _knownIrregularInfinitives.contains(l)) {
        out.add(l);
      }
    }

    return out;
  }

  // =========================
  // INFLESSIONE VERBI REGOLARI PER TAG
  // =========================

  String? _inflectRegularVerbByTag(String infinitiveLowerKey, String tag) {
    final inf = _normalizeKey(infinitiveLowerKey);
    if (!_isInfinitive(inf)) return null;
    if (_knownIrregularInfinitives.contains(inf)) return null;

    final parts = tag.split(':');
    // Formato atteso: VER:<mood>:<tense>:<pn>
    if (parts.length != 4) return null;
    if (parts[0] != 'VER') return null;
    final mood = parts[1]; // es: ind, sub, cond, impr, ...
    final tense = parts[2]; // es: pres, impf, fut, ...
    final pn = parts[3]; // es: S2, P2, ...

    final idx = _personIndexFromPN(pn);
    if (idx == null) return null;

    final conj = _conjugationOf(inf);
    if (conj == null) return null;

    final stem = inf.substring(0, inf.length - 3);
    String pick(List<String> endings) => endings[idx];

    // INDICATIVO PRESENTE
    if (mood == 'ind' && tense == 'pres') {
      if (conj == 'are')
        return stem + pick(['o', 'i', 'a', 'iamo', 'ate', 'ano']);
      if (conj == 'ere')
        return stem + pick(['o', 'i', 'e', 'iamo', 'ete', 'ono']);
      if (conj == 'ire')
        return stem + pick(['o', 'i', 'e', 'iamo', 'ite', 'ono']);
    }

    // IMPERFETTO
    if (mood == 'ind' && tense == 'impf') {
      if (conj == 'are')
        return stem + pick(['avo', 'avi', 'ava', 'avamo', 'avate', 'avano']);
      if (conj == 'ere')
        return stem + pick(['evo', 'evi', 'eva', 'evamo', 'evate', 'evano']);
      if (conj == 'ire')
        return stem + pick(['ivo', 'ivi', 'iva', 'ivamo', 'ivate', 'ivano']);
    }

    // FUTURO
    if (mood == 'ind' && tense == 'fut') {
      final futStem = _futureStem(inf, conj);
      return futStem + pick(['ò', 'ai', 'à', 'emo', 'ete', 'anno']);
    }

    // CONDIZIONALE PRESENTE
    if (mood == 'cond' && tense == 'pres') {
      final condStem = _futureStem(inf, conj);
      return condStem + pick(['ei', 'esti', 'ebbe', 'emmo', 'este', 'ebbero']);
    }

    // CONGIUNTIVO PRESENTE
    if (mood == 'sub' && tense == 'pres') {
      if (conj == 'are')
        return stem + pick(['i', 'i', 'i', 'iamo', 'iate', 'ino']);
      return stem + pick(['a', 'a', 'a', 'iamo', 'iate', 'ano']);
    }

    // CONGIUNTIVO IMPERFETTO (base)
    if (mood == 'sub' && tense == 'impf') {
      if (conj == 'are') {
        return stem +
            pick(['assi', 'assi', 'asse', 'assimo', 'aste', 'assero']);
      }
      if (conj == 'ere') {
        return stem +
            pick(['essi', 'essi', 'esse', 'essimo', 'este', 'essero']);
      }
      if (conj == 'ire') {
        return stem +
            pick(['issi', 'issi', 'isse', 'issimo', 'iste', 'issero']);
      }
    }

    // IMPERATIVO PRESENTE (supporta i casi usati nei tuoi log: S2 / P2)
    if (mood == 'impr' && tense == 'pres') {
      // idx: S1=0,S2=1,S3=2,P1=3,P2=4,P3=5
      if (conj == 'are') return stem + pick(['', 'a', '', '', 'ate', '']);
      if (conj == 'ere') return stem + pick(['', 'i', '', '', 'ete', '']);
      if (conj == 'ire') return stem + pick(['', 'i', '', '', 'ite', '']);
    }

    return null;
  }

  int? _personIndexFromPN(String pn) {
    if (pn.length != 2) return null;
    final sp = pn[0]; // S / P
    final p = int.tryParse(pn.substring(1));
    if (p == null || p < 1 || p > 3) return null;

    if (sp == 'S') return p - 1; // 0..2
    if (sp == 'P') return 3 + (p - 1); // 3..5
    return null;
  }

  String _futureStem(String inf, String conj) {
    // semplificato: are -> er (parlare -> parler-), ere/ire -> r (temere->temer-, finire->finir-)
    if (conj == 'are') {
      final s = inf.substring(0, inf.length - 3);
      return s + 'er';
    }
    return inf.substring(0, inf.length - 1);
  }

  bool _isInfinitive(String w) {
    final ww = _normalizeKey(w);
    final conj = _conjugationOf(ww);
    if (conj == null) return false;

    // Irregolari “noti” (se li vuoi comunque trattare come verbi)
    if (_knownIrregularInfinitives.contains(ww)) return true;

    // Verbo solo se la morfologia lo conosce come infinito
    return _verbInfinitives.contains(ww);
  }

  String? _conjugationOf(String w) {
    if (w.endsWith('are')) return 'are';
    if (w.endsWith('ere')) return 'ere';
    if (w.endsWith('ire')) return 'ire';
    return null;
  }

  // =========================
  // LEMMI TRONCHI + CLITICI
  // =========================

  _LemmaPrep _prepareLemmaForLookup(String lemmaLower) {
    final original = _normalizeKey(lemmaLower);

    // tronco tipo "andar" -> "andare"
    if (original.endsWith('r') && !original.endsWith('re')) {
      final expanded = original + 'e';
      if (_isInfinitive(expanded)) {
        return _LemmaPrep(
          original: original,
          lookup: expanded,
          truncatedInfinitive: true,
        );
      }
    }

    return _LemmaPrep(
      original: original,
      lookup: original,
      truncatedInfinitive: false,
    );
  }

  String _maybeRetruncateInfinitive(String lowerLemma) {
    // "andare" -> "andar"
    if (_isInfinitive(lowerLemma)) {
      return lowerLemma.substring(0, lowerLemma.length - 1);
    }
    return lowerLemma;
  }

  _CliticSplit _splitClitic(String lowerWordKey) {
    lowerWordKey = _normalizeKey(lowerWordKey);
    String? best;
    for (final c in _clitics) {
      if (c.isEmpty) continue;
      if (lowerWordKey.length <= c.length) continue;
      if (!lowerWordKey.endsWith(c)) continue;
      if (best == null || c.length > best.length) best = c;
    }

    if (best == null) {
      return _CliticSplit(lemma: lowerWordKey, clitic: null);
    }

    final base = lowerWordKey.substring(0, lowerWordKey.length - best.length);
    if (!_looksLikeCliticAttachableBase(base)) {
      return _CliticSplit(lemma: lowerWordKey, clitic: null);
    }
    return _CliticSplit(lemma: base, clitic: best);
  }

  bool _looksLikeCliticAttachableBase(String base) {
    if (base.isEmpty) return false;
    if (base.endsWith("'")) return true;

    final vowelEnd =
        RegExp(r"[aeiouàèéìòóù]$", caseSensitive: false, unicode: true);
    if (vowelEnd.hasMatch(base)) return true;

    // base tronca tipo "andar", "far"...
    if (base.endsWith('r')) {
      if (base.length >= 4) return true;
      if (_allowedTruncatedInfinitives.contains(base)) return true;
      return false;
    }

    return false;
  }

  // =========================
  // ELISIONI
  // =========================

  bool _isApostrophe(String ch) => ch == "'" || ch == '’';

  String? _tryReadFixedElisionPrefix(String text, int startIndex) {
    var j = startIndex;
    if (j >= text.length || !_isLetter(text[j])) return null;

    while (j < text.length && _isLetter(text[j])) {
      j++;
    }

    if (j >= text.length || !_isApostrophe(text[j])) return null;

    final rawPrefix = text.substring(startIndex, j + 1);
    final normalizedLower = rawPrefix.replaceAll('’', "'").toLowerCase();
    if (_fixedElisionPrefixes.contains(normalizedLower)) {
      return rawPrefix.replaceAll('’', "'");
    }

    return null;
  }

  bool _startsWithVowelOrH(String lowerWord) {
    if (lowerWord.isEmpty) return false;
    final re = RegExp(r'^[aeiouàèéìòóùh]', caseSensitive: false, unicode: true);
    return re.hasMatch(lowerWord);
  }

  // =========================
  // LETTERE / CASE
  // =========================

  bool _isLetter(String ch) {
    final code = ch.codeUnitAt(0);
    if ((code >= 65 && code <= 90) || (code >= 97 && code <= 122)) {
      return true; // A-Z a-z
    }
    if (code >= 192 && code <= 687) {
      return true; // esteso latin-1 + latin extended
    }
    return false;
  }

  bool _isUpper(String ch) => ch.toUpperCase() == ch && ch.toLowerCase() != ch;

  String _adjustCaseLike(String source, String target) {
    if (source.isEmpty || target.isEmpty) return target;
    final isAllUpper =
        source.toUpperCase() == source && source.toLowerCase() != source;
    if (isAllUpper) return target.toUpperCase();

    final isCapitalized = _isUpper(source[0]);
    if (isCapitalized) {
      return target[0].toUpperCase() + target.substring(1);
    }

    return target;
  }

  // =========================
  // DEBUG PRINT
  // =========================

  void _dPrint(String where, String msg) {
    var m = msg;
    if (m.length > _debugTruncate) {
      m = m.substring(0, _debugTruncate) + '...';
    }
    // ignore: avoid_print
    print('[KiaroCipher/$where] $m');
  }

  // =========================
  // NORMALIZZAZIONE (invisibili/bidi robusta)
  // =========================

  static bool _isInvisibleRune(int r) {
    // ASCII control + C1 controls
    if (r <= 0x1F) return true;
    if (r >= 0x7F && r <= 0x9F) return true;

    // spazi speciali comuni
    if (r == 0x00A0 || r == 0x202F || r == 0x205F || r == 0x3000) return true;

    // soft hyphen + combining grapheme joiner + arabic letter mark, etc.
    if (r == 0x00AD || r == 0x034F || r == 0x061C || r == 0x180E) return true;

    // zero-width + marks vari
    if (r >= 0x200B && r <= 0x200F) return true; // ZWSP..RLM
    if (r >= 0x202A && r <= 0x202E) return true; // LRE..RLO/PDF range
    if (r >= 0x2060 && r <= 0x206F)
      return true; // word joiner + bidi isolates + invisibili vari
    if (r == 0xFEFF) return true; // BOM/ZWNBSP

    // interlinear annotation (invisibili)
    if (r >= 0xFFF9 && r <= 0xFFFB) return true;

    // shorthand format controls
    if (r >= 0x1BCA0 && r <= 0x1BCA3) return true;

    // TAG characters block (usati raramente, ma sono invisibili)
    if (r >= 0xE0000 && r <= 0xE007F) return true;

    return false;
  }

  static String _stripInvisiblesKeepCase(String s) {
    final sb = StringBuffer();
    for (final r in s.runes) {
      if (_isInvisibleRune(r)) continue;
      sb.writeCharCode(r);
    }
    return sb.toString();
  }

  static String _normalizeKey(String s) {
    var x = s.replaceAll('’', "'");
    x = _stripInvisiblesKeepCase(x);
    x = x.toLowerCase();
    return x.trim();
  }

  static Map<String, String> _normalizeStringMapKeys(
      Map<String, String> input) {
    final out = <String, String>{};
    input.forEach((k, v) {
      out[_normalizeKey(k)] = _normalizeKey(v);
    });
    return out;
  }

  static Map<String, List<Map<String, String>>> _normalizeFormToLemmaTags(
    Map<String, List<Map<String, String>>> input,
  ) {
    final out = <String, List<Map<String, String>>>{};
    input.forEach((form, analyses) {
      final f = _normalizeKey(form);
      final list = <Map<String, String>>[];
      for (final a in analyses) {
        final m = <String, String>{};
        a.forEach((k, v) {
          final kk = k.toString();
          final vv = v.toString();
          if (kk == 'lemma') {
            m[kk] = _normalizeKey(vv);
          } else if (kk == 'tag' || kk == 'tags') {
            m[kk] = vv.trim();
          } else {
            m[kk] = vv;
          }
        });
        list.add(m);
      }
      out[f] = list;
    });
    return out;
  }

  static Map<String, Map<String, String>> _normalizeLemmaTagToForm(
    Map<String, Map<String, String>> input,
  ) {
    final out = <String, Map<String, String>>{};
    input.forEach((lemma, tagMap) {
      final l = _normalizeKey(lemma);
      final inner = <String, String>{};
      tagMap.forEach((tag, form) {
        inner[tag.toString().trim()] = _normalizeKey(form.toString());
      });
      out[l] = inner;
    });
    return out;
  }
}

// =========================
// SUPPORT CLASSES
// =========================

class _CliticSplit {
  final String? lemma;
  final String? clitic;

  _CliticSplit({required this.lemma, required this.clitic});
}

class _LemmaPrep {
  final String original; // come in input (normalizzato)
  final String lookup; // espanso (es: andar -> andare)
  final bool truncatedInfinitive;
  _LemmaPrep({
    required this.original,
    required this.lookup,
    required this.truncatedInfinitive,
  });
}
