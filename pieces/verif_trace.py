# -*- coding: utf-8 -*-
"""Vérifie la preuve de la réécriture du 11 novembre 2026 : KRY propose seule une nouvelle version
de son organe de rappel, scellée avant que ses épreuves existent, puis tirées d'un hasard public.

    python verif_trace.py [trace_reecriture.jsonl]

Ce que ce programme contrôle, sans rien installer (Python 3.9 ou plus, bibliothèque standard) :
  1. chaque ligne est scellée : son empreinte h est le SHA-256 de la ligne sans h, en JSON canonique
     (clés triées, sans espaces, UTF-8) ; chaque ligne porte l'empreinte de la précédente (prec) ;
  2. le tirage public : l'aléa de la ligne « revelation » est le hasard drand (quicknet) de la ronde
     annoncée, lu sur api.drand.sh ; cette ronde a été émise après la ligne « engagement » ;
  3. le verdict : note du champion, note du candidat, duels gagnés et perdus, rétention ;
  4. la promotion : le verdict qu'elle cite est bien celui de ce candidat.
Ce qu'il ne contrôle pas : refaire les 128 épreuves (elles se tirent dans la mémoire de KRY, qui
n'est pas publiée) ; la signature BLS de drand (on se fie à son serveur public).
Sortie 0 si tout passe, 1 sinon.
"""
import hashlib
import json
import pathlib
import sys
import urllib.request
from datetime import datetime, timezone

ici = pathlib.Path(__file__).resolve().parent


def canonique(objet):
    return json.dumps(objet, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode("utf-8")


def drand(chaine, chemin):
    with urllib.request.urlopen(f"https://api.drand.sh/{chaine}/{chemin}", timeout=20) as r:
        return json.load(r)


def main():
    fichier = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else ici / "trace_reecriture.jsonl"
    lignes = [json.loads(l) for l in fichier.read_text(encoding="utf-8").splitlines() if l.strip()]
    echecs = []

    def ok(condition, quoi):
        print(("OK     " if condition else "ÉCHEC  ") + quoi)
        if not condition:
            echecs.append(quoi)

    # 1. la chaîne
    for i, l in enumerate(lignes):
        h = hashlib.sha256(canonique({k: v for k, v in l.items() if k != "h"})).hexdigest()
        ok(h == l["h"], f"ligne {l['n']} ({l['genre']}) : empreinte recalculée")
        if i:
            ok(l["prec"] == lignes[i - 1]["h"], f"ligne {l['n']} : porte l'empreinte de la ligne {lignes[i - 1]['n']}")

    par_genre = {l["genre"]: l for l in lignes}
    eng, rev, ver, pro = (par_genre[g] for g in ("engagement", "revelation", "verdict", "promotion"))
    candidat = eng["corps"]["candidats"][0]

    # 2. le tirage public
    ok(rev["corps"]["engagement"] == eng["n"], "la révélation répond à cet engagement")
    ok(rev["corps"]["ronde"] == eng["corps"]["balise_avant"]["ronde"] + 1,
       "les épreuves viennent de la ronde suivant la dernière connue à l'engagement")
    chaine = rev["corps"]["url"].split("/")[3]
    try:
        info = drand(chaine, "info")
        public = drand(chaine, f"public/{rev['corps']['ronde']}")
    except OSError as e:
        print(f"(drand injoignable : {e} ; contrôle du tirage sauté)")
        echecs.append("drand injoignable")
    else:
        ok(public["randomness"] == rev["corps"]["alea"], f"ronde {public['round']} : l'aléa est bien le hasard public drand")
        emise = info["genesis_time"] + (rev["corps"]["ronde"] - 1) * info["period"]
        scelle = datetime.fromisoformat(eng["t"]).timestamp()
        print(f"       engagement scellé : {eng['t']} ; ronde émise : "
              f"{datetime.fromtimestamp(emise, timezone.utc).isoformat()}")
        ok(scelle < emise, f"le candidat est scellé {emise - scelle:.0f} s avant que le hasard existe")

    # 3. le verdict
    c = ver["corps"]
    ok(c["engagement"] == eng["n"] and c["candidat"] == candidat, "le verdict juge ce candidat, sur cet engagement")
    ok(c["n"] == eng["corps"]["nombre"], f"{c['n']} épreuves jouées")
    print(f"       note : champion {c['champion']}, candidat {c['note']} ; duels : {c['gagnes']} gagnés, "
          f"{c['perdus']} perdus ; rétention {c['retention']}")
    ok(c["accepte"] and c["note"] > c["champion"] and c["perdus"] == 0 and c["retention"] == 1.0,
       "le candidat est meilleur, ne perd aucun duel et ne perd rien de ce qui était acquis")

    # 4. la promotion
    ok(pro["corps"]["verdict"] == ver["n"] and pro["corps"]["organes"] == candidat,
       f"promotion validée par un humain, sur ce verdict (commit {pro['corps']['commit'][:7]})")

    print("\nTout passe." if not echecs else f"\n{len(echecs)} échec(s).")
    return 1 if echecs else 0


if __name__ == "__main__":
    sys.exit(main())
