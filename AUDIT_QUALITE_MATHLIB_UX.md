# Audit de qualité — bibliothèque Random Trees

> **Mise à jour après mise en œuvre — 2 novembre 2026.** Les sections 1 à 8 conservent
> le constat initial. Les corrections ont depuis été appliquées et vérifiées : voir la
> section 9 et le [rapport de formalisation](FORMALIZATION_REPORT.md).

Audit du **2 novembre 2026**, sur le dossier `BGW-formalization`, avec trois revues
indépendantes : architecture/API, documentation/expérience utilisateur et sémantique ciblée.
Le coordinateur a exécuté les contrôles Lean. Ce rapport est un instantané ;
`FORMALIZATION_REPORT.md` doit rester la référence de couverture après sa mise à jour.

## 1. Verdict

**Le projet possède un socle mathématique et architectural sérieux, mais il n'atteint pas
encore les plus hauts standards d'une bibliothèque Lean prête à être largement réutilisée.**
Les principaux écarts concernent la frontière de livraison, la validation continue et
l'expérience du lecteur. Ils ne justifient ni de changer la représentation des arbres,
ni de refaire les quotients GHP, ni de créer plusieurs packages.

Il faut distinguer trois objectifs :

| Objectif | Conclusion de cet audit |
| --- | --- |
| Utiliser la bibliothèque avec son Mathlib fixé | L'interface publique compile avec Lean 4.35.0 et le pin actuel. |
| Livrer une bibliothèque maintenable et agréable à réutiliser | Encore des corrections nécessaires : un module hors interface échoue, documentation contradictoire, contrôles peu durables, parcours consommateur incomplet. |
| Contribuer certains résultats à Mathlib | Perspective crédible pour de petits résultats génériques ; le dépôt entier n'est pas prêt à être intégré tel quel. L'acceptation relève aussi des mainteneurs. |

Mathlib attend généralité, intégration, maintenabilité et documentation ; sa documentation
recommande aussi les bibliothèques indépendantes pour certains développements spécialisés.
La stratégie raisonnable est donc **une bonne bibliothèque autonome, puis des contributions
ciblées**, sans faire de l'intégration totale un préalable.
[Référence officielle : contribuer à Mathlib](https://leanprover-community.github.io/contribute/index.html).

## 2. Périmètre et résultats vérifiés

Environnement : Lean **4.35.0**, Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`, HEAD
`d818312f05742621cf0c5b76fca124c93ff1572e`, avec les modifications locales présentes.
Aucune preuve, configuration, dépendance ou documentation antérieure n'a été modifiée
pendant cet audit. Seul ce rapport est ajouté ; les probes et logs sont temporaires.

| Contrôle effectué | Résultat et limite |
| --- | --- |
| `lake build` | **Réussite, 3 603 tâches, sans avertissement.** Build incrémental de l'interface par défaut, pas compilation de chaque source présente. |
| Probe consommateur avec seulement `import BGW`, sans `import all` | **Réussite.** Les trois exemples Lean du README, les instances de probabilité BGW et de complétude/Polish/Borel GHP enracinée, le codage en arbre réel et la loi image Vervaat passent. Les exports C2, variance finie et indépendance de la régression sont accessibles. Ce n'est pas un test d'installation depuis un autre projet. |
| Compilation explicite de `BrownianBridgeGrid`, `BrownianBridgeMinimum`, `MarchalWeights` | Grid : réussite ; Marchal : réussite avec un avertissement de variable de section inutilisée ; Minimum : échec. La commande commune termine donc en échec. |
| Audit transitif des axiomes, imports `all` incluant les déclarations privées/générées | **3 169 déclarations de 169 modules**, uniquement `propext`, `Classical.choice`, `Quot.sound`. Périmètre : 139 modules BGW et les 30 modules fournisseurs. **Minimum est exclu**, puisqu'il ne compile pas. |
| `#lint only docBlame in BGW` sur cette fermeture | **27 signalements** de définitions ou champs sans docstring. Le probe combinant axiomes et ce linter termine en échec à cause du linter, après réussite du contrôle des axiomes. |
| Scan lexical ignorant commentaires et chaînes | Aucun `sorry`, `admit`, `axiom`, `native_decide`, `bv_decide` ou `unsafe` dans les 170 sources BGW/fournisseurs examinées. Cela ne fait pas compiler le fichier inachevé. |
| Inventaire des imports | 140 fichiers BGW, 22 610 lignes ; `import BGW` atteint 137 modules BGW. Les trois modules ci-dessus sont hors de sa fermeture. |
| Documentation et hygiène | Liens locaux des quatre documents principaux résolus ; `git diff --check` réussi. Tous les fichiers BGW ont une documentation de module. |

Les nombres de tâches Lake ne sont pas des nombres de modules propres au projet.
L'audit d'axiomes vérifie une frontière de confiance formelle ; il ne démontre pas à lui seul
que chaque énoncé traduit exactement un article. La revue sémantique a été ciblée sur les
interfaces sensibles, sans certification exhaustive des 22 610 lignes.

Non vérifié ici : clone propre sur une autre machine, exécution distante de GitHub Actions,
compatibilité avec une autre version de Mathlib, ensemble complet des linters Mathlib,
performances à froid et fidélité de chaque résultat à toutes les sources bibliographiques.

## 3. Ce qui est déjà bien conçu

### Des objets réels et des interfaces réutilisables

- **Arbres finis :** `WType` reste confiné à [Tree.lean](BGW/Tree.lean).
  Les utilisateurs disposent de `node`, `children`, `fold`, d'une induction adaptée et
  d'équations `[simp]`. Le choix interne n'impose pas une réécriture des preuves clientes.
- **Arbres localement finis :** le porteur canonique, la topologie polonaise, la loi BGW,
  son unicité et le pont vers les arbres finis sont effectivement construits.
  L'absence d'un sommet est distinguée d'une feuille.
- **GHP :** le quotient utilise des isométries de l'espace entier ; dans le cas enraciné,
  une même isométrie préserve la mesure et la racine. Il n'exige pas le plein support.
  La complétude utilise la métrique déjà définie, sans métrique de remplacement.
  Voir [RootedMeasuredGHSpace](BGW/MetricMeasure/RootedMeasuredGHSpace.lean) et
  [RootedGHPCompleteness](BGW/MetricMeasure/RootedGHPCompleteness.lean).
- **Instances :** la métrique des sommets est portée par `Vertex t`, et le changement
  d'échelle par `ScaledMetric`. Aucune métrique globale artificielle sur toutes les adresses
  n'est introduite. Les structures boréliennes sont compatibles avec les topologies.
- **Probabilités :** le pont brownien vient d'une véritable construction ; le transfert
  [C2 en loi](BGW/ContinuumTrees/ContourLawConvergence.lean) déduit l'erreur GHP de la
  tension et du contrôle des contours. Il ne la prend pas comme hypothèse cachée.
- **Dépendances :** imports Mathlib ciblés, versions fixées, sources Brownian/Kolmogorov
  vendoriées avec licences et provenance. Aucune option `set_option` dans les sources BGW ;
  aucun gonflement local du budget de heartbeats observé.

### Des frontières mathématiques honnêtes

Ces distinctions doivent être conservées dans toutes les futures présentations :

| Résultat disponible | Ce qu'il ne prouve pas encore |
| --- | --- |
| Loi du pont, transformation de Vervaat mesurable et loi de l'arbre codé | Identification à l'excursion standard et à la CRT brownienne classique. |
| Minimum du pont strictement négatif presque sûrement, dans Grid | Unicité du minimiseur continu. |
| Transfert de convergence des contours vers la convergence GHP | Principe d'invariance des contours d'arbres conditionnés. |
| `StableDomain`, LLT, variation régulière et cas de variance finie | Construction d'un processus de Lévy stable, de son excursion de hauteur ou d'un arbre stable continu. |
| PMF de sélection de Marchal sur un graphe fourni | Construction de la chaîne de croissance, loi exacte de l'arbre ou identification avec Rémy. |

Ces limites sont explicites dans [VervaatBridge](BGW/ContinuumTrees/VervaatBridge.lean),
[StableTrees](BGW/StableTrees.lean) et [MarchalWeights](BGW/StableTrees/MarchalWeights.lean).
Je n'ai pas relevé de faux énoncé dans les interfaces échantillonnées ; les travaux
probabilistes restants sont néanmoins substantiels.

## 4. Corrections prioritaires

### P1 — Définir et vérifier exactement ce qui est livré

**Le build par défaut laisse passer un fichier Lean qui échoue.**
[BrownianBridgeMinimum.lean](BGW/ContinuumTrees/BrownianBridgeMinimum.lean), lignes 69,
105 et 120, présente respectivement une erreur de syntaxe, un identifiant inconnu
`measure_prod_null_of_ae_null` et un but non résolu. Il n'est pas importé par l'agrégateur,
donc cet échec ne contamine pas les résultats publics qui compilent.

Le [workflow actuel](.github/workflows/lean.yml), lignes 25–30, exécute essentiellement le
build par défaut. **Une CI verte ne signifie donc pas ici que toutes les sources BGW
présentes sont vérifiées.** Corriger le module, puis faire vérifier les modules de la
bibliothèque même s'ils ne sont pas réexportés. Si un travail reste volontairement inachevé,
son exclusion doit être explicite et visible, sans le présenter comme résultat disponible.
Inutile de créer un dispositif de manifeste par théorème.

[MarchalWeights.lean](BGW/StableTrees/MarchalWeights.lean), ligne 56, compile mais conserve
un avertissement `unusedSectionVars` sur `[DecidableEq V]`. Le supprimer sans modifier
la portée mathématique du résultat. Exporter Grid ou Marchal est ensuite un choix d'API,
pas une condition pour que leurs preuves soient valides par import direct.

### P1 — Réconcilier documentation, code et historique

Le [README](README.md), lignes 85–86, et le [rapport](FORMALIZATION_REPORT.md), autour des
lignes 120–128, disent encore que la complétude enracinée reste ouverte. La
[roadmap](RANDOM_TREES_ROADMAP.md), lignes 110–112, laisse aussi ouverts cette complétude et
le transfert C2 en loi avec tailles aléatoires. Ces résultats sont désormais importés
et compilent dans l'interface publique.

Mettre à jour ces passages, en distinguant **disponible**, **en cours** et **objectif**.
Conserver les anciens comptes de vérification comme historiques datés. Le handover ne
doit pas être nécessaire pour corriger mentalement les affirmations du README.

### P1 avant livraison — Enregistrer un ensemble reproductible

Sur les 140 fichiers BGW, **9 seulement sont actuellement suivis par Git** ; les 30 sources
vendoriées ne le sont pas. Les nouvelles entrées sectorielles, la roadmap commune et le
handover sont aussi non suivis. Le commit actuel seul ne reproduit donc pas cet état local.

Préparer ultérieurement un ensemble cohérent de sources, configurations, licences et
documentation pour la livraison. Ce constat porte sur le dépôt local ; il ne prétend pas
décrire le contenu d'un distant non inspecté. Aucun commit ou push n'a été effectué ici.

### P2 — Rendre les vérifications durables et adaptées à Mathlib

Les probes d'axiomes et d'utilisation actuels résident dans `/tmp`. Leur qualité est utile,
mais ils ne protègent pas durablement les futurs changements. Conserver quelques exemples
consommateurs significatifs et un petit contrôle d'axiomes reproductible, puis les exécuter
dans le workflow existant. Les exemples doivent utiliser les imports publics ordinaires ;
le contrôle des axiomes peut employer `import all` pour inspecter les détails internes.

Le [lakefile](lakefile.toml) ne configure que `autoImplicit = false`. Il n'active pas le
jeu standard des linters Mathlib. Le Mathlib fixé documente précisément cette activation
dans [Mathlib/Init.lean](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Init.lean#L85), lignes 85–86.
Activer les contrôles pertinents après un relevé des écarts, sans désactiver globalement
les avertissements pour obtenir artificiellement du vert.

Le contrôle `docBlame` a relevé **27 manques**, dont `LocallyFinite.degree`,
`toMeasuredGHSpace`, `toRootedMeasuredGHSpace`, plusieurs champs des espaces mesurés,
les conversions de `ScaledMetric` et `finiteVarianceLaw`. Ces omissions affectent le
survol dans l'éditeur et la compréhension des conversions. Une courte docstring
mathématique suffit ; inutile de commenter chaque étape de preuve.
[Référence officielle : documentation](https://leanprover-community.github.io/contribute/doc.html).

Enfin, 12 fichiers BGW n'ont pas d'en-tête copyright et aucun des 140 ne contient de
champ `Authors:` dans l'en-tête. Le dépôt possède une licence globale et les fournisseurs
conservent leurs notices : il s'agit ici d'un écart aux conventions de contribution,
pas d'une conclusion d'absence de licence. Renseigner fidèlement les auteurs et les
provenances, sans les inventer. Les 34 lignes BGW dépassant 100 caractères sont une
finition secondaire ; le fichier le plus long ne fait que 618 lignes.
[Référence officielle : style](https://leanprover-community.github.io/contribute/style.html).

## 5. Imbrication des directions et expérience utilisateur

L'organisation actuelle permet déjà de distinguer les principaux parcours d'utilisation :

| Parcours | Socle utilisé | Import utile pour commencer |
| --- | --- | --- |
| Combinatoire des arbres finis | Mathlib `WType`, listes et finitude | `BGW.Tree`, puis `BGW.Tree.Excursion` ou `BGW.Tree.Geometry` selon le besoin |
| Lois BGW | Arbres localement finis, produits de mesures, pont avec les arbres finis | `BGW.LocallyFinite.Law` ou `BGW.LocallyFinite.SizeConditioning` |
| Géométrie GHP et arbres continus | Espaces métriques mesurés ; contours finis pour le transfert ; fournisseur brownien pour la partie aléatoire | `BGW.MetricMeasure`, `BGW.ContinuumTrees.CodingMeasure` ou `BGW.ContinuumTrees.ContourLawConvergence` |
| Outils stables | Lois de marches, analyse scalaire ; identité forestière BGW pour les estimations | `BGW.StableTrees` ; imports plus fins pour la variation régulière |

Cette table exprime les dépendances conceptuelles, pas un graphe exhaustif des imports.
`import BGW` reste une commodité légitime, mais atteint toutes les directions, y compris
le fournisseur brownien. Sa fermeture compte 137 modules BGW, contre un seul pour
`BGW.Tree`, hors dépendances Mathlib. **Aucun gain de temps n'a été mesuré** : l'intérêt
immédiat des imports fins est de rendre les dépendances et la lecture plus claires.

Pour une meilleure prise en main, les améliorations utiles sont petites :

1. Mettre un premier exemple compilé près du début du README, avant le long inventaire.
2. Ajouter une recette Lake pour un projet consommateur, avec URL réelle et commit fixé
   au moment de la livraison ; ne pas fournir une adresse ou une révision fictive.
3. Montrer un exemple BGW probabiliste, un exemple GHP/codage et un exemple stable scalaire.
   Les trois exemples actuels ne couvrent que les arbres finis.
4. Regrouper les conventions sensibles dans une table courte, avec liens vers les définitions.
5. Ajouter une courte section de contribution : pins, contrôles, documentation et absence
   de trous de preuve. Le handover entre assistants n'est pas un guide de contribution.

La table de conventions devrait rappeler : indices finis à partir de zéro et indices
localement finis positifs ; taille comptant les sommets ; masse uniforme sur **tous** les
sommets ; contour sur l'intervalle unité ; GHP défini par somme des coûts ; espace entier
conservé même hors support de la mesure ; normalisation brownienne $T_{2e}$ ; limite
scalaire de variance $2$ au cas stable $\alpha=2$ ; conditionnement aux tailles admissibles.

Deux améliorations d'API méritent un essai limité :

- Un lemme d'extensionalité par les enfants pour `PlaneTree`, motivé par un exemple
  consommateur. L'égalité est déjà accessible via `equivChildren` ; l'absence de `@[ext]`
  n'est pas une erreur mathématique. Ne pas ajouter cet attribut partout.
- Un exemple probabiliste traitant explicitement la mesurabilité des observables du
  transfert C2. L'absence d'instance globale `MeasurableSpace PlaneTree` est un choix
  assumé ; ne pas modifier ce choix pour masquer les obligations de l'exemple.

## 6. Préparer de futures contributions à Mathlib

Un candidat concret au découplage est
[RootedScalingBase.lean](BGW/MetricMeasure/RootedScalingBase.lean), ligne 7 : il importe
le quotient enraciné alors que son changement d'échelle et ses bornes Hausdorff/Prokhorov
sont génériques. Sa fermeture atteint 19 modules BGW, lui compris. Réduire cette dépendance,
un module à la fois et à signatures conservées, aiderait un consommateur extérieur à GHP.

Les bornes génériques Hausdorff/Prokhorov, certains lemmes de variation régulière et le
transfert par perturbation faible sont des **candidats à examiner**, après recherche des
équivalents déjà disponibles. Ce rapport ne constate pas leur absence du Mathlib actuel
et ne prédit pas leur acceptation. Les contributions doivent utiliser les namespaces et
conventions correspondant à leur contenu mathématique.
[Référence officielle : nommage](https://leanprover-community.github.io/contribute/naming.html).

Les dépendances Brownian externes conviennent à une bibliothèque autonome. Une contribution
à Mathlib doit en revanche être isolée dans une chaîne de dépendances adaptée à Mathlib.
Commencer par de petits résultats indépendants évite de coupler une proposition utile à
l'intégration préalable de toute la théorie brownienne.

Pour une future soumission, prévoir une personne capable d'expliquer et de maintenir le
code. La politique actuelle de Mathlib exige de déclarer l'usage d'outils d'IA et souligne
la nécessité de supervision compétente. Les commentaires publics GitHub/Zulip doivent
être rédigés par le contributeur lui-même.
[Politique officielle de contribution](https://leanprover-community.github.io/contribute/index.html#use-of-ai).

## 7. Roadmap minimale pour des agents d'effort moindre

Cette roadmap prépare la qualité de la bibliothèque ; elle ne rouvre pas implicitement
le chantier de formalisation de tous les articles. Les lots sont petits, avec un seul
coordinateur Lean/Lake. Les agents travaillent sur des fichiers distincts ; les résultats
mathématiques nouveaux ne sont pas des tâches de nettoyage.

| Lot | Effort conseillé | Travail borné | Critère d'acceptation |
| --- | --- | --- | --- |
| A — Frontière compilable | Moyen, avec revue finale plus attentive | Réparer Minimum sans changer son énoncé ; supprimer l'avertissement Marchal ; décider et documenter les exports. | Build public et contrôle de chaque module destiné à être livré réussis ; audit des axiomes incluant Minimum après réparation. Si une nouvelle idée mathématique est nécessaire, isoler cette difficulté pour une revue approfondie. |
| B — Statuts et parcours lecteur | Faible | Synchroniser README/rapport/roadmap ; ajouter table d'imports et conventions ; déplacer le premier exemple vers le début. | Aucune contradiction entre documents et résultats vérifiés ; liens valides ; limites CRT/stable toujours explicites. Dépend des résultats de A pour ces deux modules. |
| C — Documentation locale et style | Faible | Traiter les 27 signalements `docBlame`, les en-têtes et les références opaques ; respecter les auteurs réels. | Linter documentaire propre sur le périmètre livré ; aucun énoncé ni preuve modifié pour ce lot. Peut avancer parallèlement à B sur les fichiers Lean. |
| D — Régressions et CI | Moyen | Conserver quelques exemples publics et un audit d'axiomes relançable ; couvrir tous les modules livrés dans le workflow existant ; activer progressivement les linters utiles. | Une rupture d'export ou un module livré non compilable est détecté ; exemples exécutés sans `import all`. Pas de tests recopiant chaque théorème. |
| E — Petites améliorations d'API | Moyen | Essayer l'extensionalité par enfants et un parcours probabiliste ; alléger les imports génériques de scaling seulement si utile. | Un exemple consommateur devient plus simple ; signatures existantes conservées ; consommateurs recompilés. À différer si aucun bénéfice concret. |
| F — Préparation de livraison | Faible pour l'inventaire, coordinateur pour la validation | Vérifier l'ensemble des sources/configurations/licences à enregistrer et la recette de dépendance. | Validation depuis l'ensemble réellement destiné à être partagé ; pas de dépendance à `/tmp` ou à un projet voisin. Commit/publication dans une étape distincte. |

Ordre conseillé : **A, puis B et C en parallèle, puis D ; E est optionnel ; F clôt la
préparation.** Le coordinateur donne aux agents d'effort faible une liste fermée de fichiers
et de corrections, puis vérifie le diff. Aucun changement de pin ni renommage global.

Garder un effort élevé pour les véritables décisions mathématiques : identification
Vervaat–excursion–CRT, porteur et loi exacte de Marchal, compatibilité des normalisations,
construction des processus stables et principes d'invariance. Les déléguer comme des
retouches mécaniques risquerait de modifier le sens des résultats.

Ne pas ajouter maintenant : portail de documentation, nouvelle base de données de preuves,
manifestes par théorème, hiérarchie générale de carriers, séparation en plusieurs packages,
nouvel encodage des arbres ou renommage massif. Une documentation générée pourra devenir
utile lorsque l'API sera plus stable ; elle n'est pas un préalable aux corrections ci-dessus.

## 8. Traces de cet audit

Les résultats ci-dessus sont consignés dans ce rapport ; les fichiers suivants sont des
traces temporaires, susceptibles de disparaître :

- `/tmp/random-trees-quality-audit-build.log` : build public réussi.
- `/tmp/random-trees-quality-audit-pending.log` : résultats des trois modules hors agrégateur.
- `/tmp/random-trees-quality-public-consumer.lean` et `random-trees-quality-public-consumer.log` :
  contrôle réussi de l'interface publique par import ordinaire.
- `/tmp/random-trees-quality-audit.lean` et `random-trees-quality-audit-axioms-docs.log` :
  contrôle d'axiomes et linter documentaire, avec échec final dû aux 27 docstrings manquantes.
- `/tmp/random-trees-quality-inventory.json` : inventaire statique.
- `/tmp/random-trees-quality-source-hashes.json` : empreintes des 170 sources examinées.

Commandes de compilation utilisées depuis la racine :

```sh
lake build
lake build BGW.StableTrees.MarchalWeights BGW.ContinuumTrees.BrownianBridgeGrid BGW.ContinuumTrees.BrownianBridgeMinimum
lake env lean /tmp/random-trees-quality-audit.lean
lake env lean /tmp/random-trees-quality-public-consumer.lean
git diff --check
```

Le probe temporaire étend le précédent contrôle aux nouveaux modules compilables,
importe les modules internes avec `import all`, inspecte les axiomes de leurs constantes
et exécute `#lint only docBlame in BGW`. Il exclut explicitement Minimum. Le lot D doit
rendre cette procédure durable ; les logs seuls ne remplacent pas une vérification future.

## 9. Mise en œuvre vérifiée — 2 novembre 2026

La roadmap de qualité a été appliquée avec les modèles et efforts demandés. Les détails
et la répartition effective figurent dans le [rapport existant](FORMALIZATION_REPORT.md#quality-and-integration-checkpoint--2-november-2026).

| Lot | Résultat |
| --- | --- |
| A — Frontière compilable | Minimum réparé sans affaiblissement ; avertissements Marchal supprimés ; Grid/Minimum/Marchal réexportés ; tous les modules construits. |
| B — Documentation | README, rapport, roadmap et handover synchronisés ; imports, conventions et usage depuis un projet local expliqués. |
| C — Docstrings et style | 27 manques corrigés ; en-têtes complétés ; référence opaque clarifiée. |
| D — Contrôles et CI | `python3 scripts/check.py` vérifie toutes les sources, deux exemples consommateurs, les axiomes et `docBlame` ; la CI appelle cette commande. |
| E — Ergonomie | `PlaneTree.ext`, exemple complet de mesurabilité locale pour C2 et imports génériques de scaling allégés, sans nouveau carrier. |
| F — Livraison | Ensemble à livrer inventorié ; caches et outils locaux exclus ; sources/configurations/licences prêtes à être enregistrées. Aucun commit ni publication ; clone propre distant non testé. |

**Validation locale réussie : 3 641 tâches Lake, 3 175 déclarations auditées dans
170 modules, zéro erreur `docBlame`, deux fichiers d'exemples publics compilés.**
Les axiomes autorisés restent `propext`, `Classical.choice` et `Quot.sound`.
Les versions Lean/Mathlib sont inchangées. Astra a relu les points mathématiques sensibles.

Ces corrections ferment les défauts de livraison et d'ergonomie traités ici. Elles ne
constituent ni une acceptation par Mathlib, ni la preuve des résultats probabilistes encore
ouverts. Le présent audit historique n'est pas un nouveau registre de suivi permanent.
