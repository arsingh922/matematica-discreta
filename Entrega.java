import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.function.BiFunction;
import java.util.function.BiPredicate;
import java.util.function.BooleanSupplier;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.IntStream;

/*
 * Aquesta entrega consisteix en implementar tots els mètodes anomenats "exerciciX". Ara mateix la
 * seva implementació consisteix en llançar `UnsupportedOperationException`, ho heu de canviar així
 * com els aneu fent.
 *
 * Criteris d'avaluació:
 *
 * - Si el codi no compila tendreu un 0.
 *
 * - Les úniques modificacions que podeu fer al codi són:
 *    + Afegir un mètode (dins el tema que el necessiteu)
 *    + Afegir proves a un mètode "tests()"
 *    + Òbviament, implementar els mètodes que heu d'implementar ("exerciciX")
 *   Si feu una modificació que no sigui d'aquesta llista, tendreu un 0.
 *
 * - Principalment, la nota dependrà del correcte funcionament dels mètodes implementats (provant
 *   amb diferents entrades).
 *
 * - Tendrem en compte la neteja i organització del codi. Un estandard que podeu seguir és la guia
 *   d'estil de Google per Java: https://google.github.io/styleguide/javaguide.html . Per exemple:
 *    + IMPORTANT: Aquesta entrega està codificada amb UTF-8 i finals de línia LF.
 *    + Indentació i espaiat consistent
 *    + Bona nomenclatura de variables
 *    + Declarar les variables el més aprop possible al primer ús (és a dir, evitau blocs de
 *      declaracions).
 *    + Convé utilitzar el for-each (for (int x : ...)) enlloc del clàssic (for (int i = 0; ...))
 *      sempre que no necessiteu l'índex del recorregut. Igualment per while si no és necessari.
 *
 * Per com està plantejada aquesta entrega, no necessitau (ni podeu) utilitzar cap `import`
 * addicional, ni qualificar classes que no estiguin ja importades. El que sí podeu fer és definir
 * tots els mètodes addicionals que volgueu (de manera ordenada i dins el tema que pertoqui).
 *
 * Podeu fer aquesta entrega en grups de com a màxim 3 persones, i necessitareu com a minim Java 10.
 * Per entregar, posau els noms i cognoms de tots els membres del grup a l'array `Entrega.NOMS` que
 * està definit a la línia 53.
 *
 * L'entrega es farà a través d'una tasca a l'Aula Digital que obrirem abans de la data que se us
 * hagui comunicat. Si no podeu visualitzar bé algun enunciat, assegurau-vos de que el vostre editor
 * de texte estigui configurat amb codificació UTF-8.
 */
class Entrega {
  static final String[] NOMS = {};

  /*
   * Aquí teniu els exercicis del Tema 1 (Lògica).
   */
  static class Tema1 {
    /*
     * Determinau si l'expressió és una tautologia o no:
     *
     * (((vars[0] ops[0] vars[1]) ops[1] vars[2]) ops[2] vars[3]) ...
     *
     * Aquí, vars.length == ops.length+1, i cap dels dos arrays és buid. Podeu suposar que els
     * identificadors de les variables van de 0 a N-1, i tenim N variables diferents (mai més de 20
     * variables).
     *
     * Cada ops[i] pot ser: CONJ, DISJ, IMPL, NAND.
     *
     * Retornau:
     *   1 si és una tautologia
     *   0 si és una contradicció
     *   -1 en qualsevol altre cas.
     *
     * Vegeu els tests per exemples.
     */
    static final char CONJ = '∧';
    static final char DISJ = '∨';
    static final char IMPL = '→';
    static final char NAND = '.';

    static int exercici1(char[] ops, int[] vars) {
       //Calcular quantes variables hi ha
    int maxVar = -1;
    for (int v : vars) {
        if (v > maxVar) {
            maxVar = v;
        }
    }
    int totalVars = maxVar + 1;
    int totalAssignacions = 1 << totalVars;
    boolean viuTrue = false;   // hem vist algun true?
    boolean viuFalse = false;  // hem vist algun false?
    //Recorregut de totes les assignacions de valors
    for (int assig = 0; assig < totalAssignacions && !(viuTrue && viuFalse); assig++) {
        // Comencem amb el valor de la primera variable
        boolean valor = ((assig >> vars[0]) & 1) == 1;
        // Anem aplicant cada operador seguit
        for (int i = 0; i < ops.length; i++) {
            boolean seguent = ((assig >> vars[i + 1]) & 1) == 1;
            char op = ops[i];
            if      (op == CONJ)  valor = valor && seguent;
            else if (op == DISJ)  valor = valor || seguent;
            else if (op == IMPL)  valor = !valor || seguent;
            else /* NAND */       valor = !(valor && seguent);
        }
        // Marcar si hem obtingut true o false
        if (valor)      viuTrue  = true;
        else            viuFalse = true;
    }
    //Determinar resultat final
    if (viuTrue && viuFalse) {
        return -1;   // ni tot true ni tot false
    }
    return viuTrue ? 1 : 0;  // 1 = tautologia, 0 = contradicció
    }

    /*
     * Aquest mètode té de paràmetre l'univers (representat com un array) i els predicats
     * adients `p` i `q`. Per avaluar aquest predicat, si `x` és un element de l'univers, podeu
     * fer-ho com `p.test(x)`, que té com resultat un booleà (true si `P(x)` és cert).
     *
     * Amb l'univers i els predicats `p` i `q` donats, returnau true si la següent proposició és
     * certa.
     *
     * (∀x : P(x)) <-> (∃!x : Q(x))
     */
    static boolean exercici2(int[] universe, Predicate<Integer> p, Predicate<Integer> q) {
          //Comproveu si P(x) es compleix per a tots els elements
    boolean allMatchP = true;
    for (int x : universe) {
        if (!p.test(x)) {
            allMatchP = false;
            break;
        }
    }
    //Compta quants elements satisfan Q(x)
    int qCount = 0;
    for (int x : universe) {
        if (q.test(x)) {
            qCount++;
            if (qCount > 1) {
                //no cal continuar un cop n'hi hagi més d'un
                break;
            }
        }
    }
    boolean exactlyOneQ = (qCount == 1);
    //Retorna "true" si coincideixen els dos costats de l'equivalència.
    return allMatchP == exactlyOneQ;
    }
    
    static void tests() {
      // Exercici 1
      // Taules de veritat

      // Tautologia: ((p0 → p2) ∨ p1) ∨ p0
      test(1, 1, 1, () -> exercici1(new char[] { IMPL, DISJ, DISJ }, new int[] { 0, 2, 1, 0 }) == 1);

      // Contradicció: (p0 . p0) ∧ p0
      test(1, 1, 2, () -> exercici1(new char[] { NAND, CONJ }, new int[] { 0, 0, 0 }) == 0);

      // Exercici 2
      // Equivalència

      test(1, 2, 1, () -> {
        return exercici2(new int[] { 1, 2, 3 }, (x) -> x == 0, (x) -> x == 0);
      });

      test(1, 2, 2, () -> {
        return exercici2(new int[] { 1, 2, 3 }, (x) -> x >= 1, (x) -> x % 2 == 0);
      });
    }
  }

  /*
   * Aquí teniu els exercicis del Tema 2 (Conjunts).
   *
   * Per senzillesa tractarem els conjunts com arrays (sense elements repetits). Per tant, un
   * conjunt de conjunts d'enters tendrà tipus int[][]. Podeu donar per suposat que tots els
   * arrays que representin conjunts i us venguin per paràmetre estan ordenats de menor a major.
   *
   * Les relacions també les representarem com arrays de dues dimensions, on la segona dimensió
   * només té dos elements. L'array estarà ordenat lexicogràficament. Per exemple
   *   int[][] rel = {{0,0}, {0,1}, {1,1}, {2,2}};
   * i també donarem el conjunt on està definida, per exemple
   *   int[] a = {0,1,2};
   * Als tests utilitzarem extensivament la funció generateRel definida al final (també la podeu
   * utilitzar si la necessitau).
   *
   * Les funcions f : A -> B (on A i B son subconjunts dels enters) les representam o bé amb el seu
   * graf o bé amb un objecte de tipus Function<Integer, Integer>. Sempre donarem el domini int[] a
   * i el codomini int[] b. En el cas de tenir un objecte de tipus Function<Integer, Integer>, per
   * aplicar f a x, és a dir, "f(x)" on x és d'A i el resultat f.apply(x) és de B, s'escriu
   * f.apply(x).
   */
  static class Tema2 {
    /*
     * Trobau el nombre de particions diferents del conjunt `a`, que podeu suposar que no és buid.
     *
     * Pista: Cercau informació sobre els nombres de Stirling.
     */
    static int exercici1(int[] a) {
    int n = a.length;
    // taula[i][k] = número de maneres de particionar i elements en k grups
    long[][] taula = new long[n + 1][n + 1];
    taula[0][0] = 1;
    // omplim la taula seguint la relació:
    for (int i = 1; i <= n; i++) {
        for (int k = 1; k <= i; k++) {
            taula[i][k] = k * taula[i - 1][k] + taula[i - 1][k - 1];
        }
    }
    // sumem totes les particions amb tots els possibles
    long totalPartitions = 0;
    for (int k = 0; k <= n; k++) {
        totalPartitions += taula[n][k];
    }
    return (int) totalPartitions;
    }

    /*
     * Trobau el cardinal de la relació d'ordre parcial sobre `a` més petita que conté `rel` (si
     * existeix). En altres paraules, el cardinal de la seva clausura reflexiva, transitiva i
     * antisimètrica.
     *
     * Si no existeix, retornau -1.
     */
    static int exercici2(int[] a, int[][] rel) {
    int n = a.length;
    boolean[][] R = new boolean[n][n];

    // Afegir relació inicial
    for (int[] p : rel) {
        int u = 0, v = 0;
        for (int i = 0; i < n; i++) {
            if (a[i] == p[0]) u = i;
            if (a[i] == p[1]) v = i;
        }
        R[u][v] = true;
    }

    // Reflexiva
    for (int i = 0; i < n; i++) R[i][i] = true;

    // Transitiva
    for (int k = 0; k < n; k++)
        for (int i = 0; i < n; i++)
            if (R[i][k])
                for (int j = 0; j < n; j++)
                    if (R[k][j]) R[i][j] = true;

    // Antisimetria
    for (int i = 0; i < n; i++)
        for (int j = i + 1; j < n; j++)
            if (R[i][j] && R[j][i])
                return -1;

    // Comptar parells
    int total = 0;
    for (int i = 0; i < n; i++)
        for (int j = 0; j < n; j++)
            if (R[i][j]) total++;

    return total;
    }

    /*
     * Donada una relació d'ordre parcial `rel` definida sobre `a` i un subconjunt `x` de `a`,
     * retornau:
     * - L'ínfim de `x` si existeix i `op` és false
     * - El suprem de `x` si existeix i `op` és true
     * - null en qualsevol altre cas
     */
    static Integer exercici3(int[] a, int[][] rel, int[] x, boolean op) {
    int n = a.length;
    // Construir la clausura reflexiva i transitiva
    boolean[][] clausura = new boolean[n][n];
    // Afegim els parells originals
    for (int[] parell : rel) {
        int from = -1, to = -1;
        for (int i = 0; i < n; i++) {
            if (a[i] == parell[0]) from = i;
            if (a[i] == parell[1])   to = i;
        }
        clausura[from][to] = true;
    }
    // Reflexiva
    for (int i = 0; i < n; i++) {
        clausura[i][i] = true;
    }
    // Transitiva
    for (int k = 0; k < n; k++)
        for (int i = 0; i < n; i++)
            if (clausura[i][k])
                for (int j = 0; j < n; j++)
                    if (clausura[k][j])
                        clausura[i][j] = true;

    // Convertir x[] en índexs dins de a[]
    int m = x.length;
    int[] xIdx = new int[m];
    for (int i = 0; i < m; i++) {
        for (int j = 0; j < n; j++) {
            if (x[i] == a[j]) {
                xIdx[i] = j;
                break;
            }
        }
    }
    // Identificar candidats
    boolean[] esCandidat = new boolean[n];
    int totalCandidats = 0;
    for (int i = 0; i < n; i++) {
        boolean ok = true;
        for (int xi : xIdx) {
            if (op) {
                // suprem
                if (!clausura[xi][i]) { ok = false; break; }
            } else {
                // ínfim
                if (!clausura[i][xi]) { ok = false; break; }
            }
        }
        if (ok) {
            esCandidat[i] = true;
            totalCandidats++;
        }
    }
    if (totalCandidats == 0) return null;
    //D’entre els candidats, triar l’únic extrem
    Integer idxResultat = null;
    for (int i = 0; i < n; i++) {
        if (!esCandidat[i]) continue;
        boolean esExtrem = true;
        for (int j = 0; j < n; j++) {
            if (i != j && esCandidat[j]) {
                if (op ? clausura[j][i] : clausura[i][j]) {
                    esExtrem = false;
                    break;
                }
            }
        }
        if (esExtrem) {
            if (idxResultat != null) {
                return null;
            }
            idxResultat = i;
        }
    }
    //Retornar el valor original
    return idxResultat == null ? null : a[idxResultat];
    }

    /*
     * Donada una funció `f` de `a` a `b`, retornau:
     *  - El graf de la seva inversa (si existeix)
     *  - Sinó, el graf d'una inversa seva per l'esquerra (si existeix)
     *  - Sinó, el graf d'una inversa seva per la dreta (si existeix)
     *  - Sinó, null.
     */
    static int[][] exercici4(int[] a, int[] b, Function<Integer, Integer> f) {
    int n = a.length;
    int m = b.length;
    //Calculem la imatge de cada element de A segons f(x)
    int[] imatge = new int[n];
    for (int i = 0; i < n; i++) {
        imatge[i] = f.apply(a[i]);
    }
    // Preparem l’array de resultats, un parell per cada y que perteneix a B
    int[][] inversa = new int[m][2];
    for (int j = 0; j < m; j++) {
        int y = b[j];
        inversa[j][0] = y;
        //Cerquem un x que pertany A amb f(x) = y
        int xAssignat = a[0];
        for (int i = 0; i < n; i++) {
            if (imatge[i] == y) {
                xAssignat = a[i];
                break;
            }
        }
        inversa[j][1] = xAssignat;
    }
    return inversa;
    }

    /*
     * Aquí teniu alguns exemples i proves relacionades amb aquests exercicis (vegeu `main`)
     */
    static void tests() {
      // Exercici 1
      // Nombre de particions

      test(2, 1, 1, () -> exercici1(new int[] { 1 }) == 1);
      test(2, 1, 2, () -> exercici1(new int[] { 1, 2, 3 }) == 5);

      // Exercici 2
      // Clausura d'ordre parcial

      final int[] INT02 = { 0, 1, 2 };

      test(2, 2, 1, () -> exercici2(INT02, new int[][] { {0, 1}, {1, 2} }) == 6);
      test(2, 2, 2, () -> exercici2(INT02, new int[][] { {0, 1}, {1, 0}, {1, 2} }) == -1);

      // Exercici 3
      // Ínfims i suprems

      final int[] INT15 = { 1, 2, 3, 4, 5 };
      final int[][] DIV15 = generateRel(INT15, (n, m) -> m % n == 0);
      final Integer ONE = 1;

      test(2, 3, 1, () -> ONE.equals(exercici3(INT15, DIV15, new int[] { 2, 3 }, false)));
      test(2, 3, 2, () -> exercici3(INT15, DIV15, new int[] { 2, 3 }, true) == null);

      // Exercici 4
      // Inverses

      final int[] INT05 = { 0, 1, 2, 3, 4, 5 };

      test(2, 4, 1, () -> {
        var inv = exercici4(INT05, INT02, (x) -> x/2);

        if (inv == null)
          return false;

        inv = lexSorted(inv);

        if (inv.length != INT02.length)
          return false;

        for (int i = 0; i < INT02.length; i++) {
          if (inv[i][0] != i || inv[i][1]/2 != i)
            return false;
        }

        return true;
      });

      test(2, 4, 2, () -> {
        var inv = exercici4(INT02, INT05, (x) -> x);

        if (inv == null)
          return false;

        inv = lexSorted(inv);

        if (inv.length != INT05.length)
          return false;

        for (int i = 0; i < INT02.length; i++) {
          if (inv[i][0] != i || inv[i][1] != i)
            return false;
        }

        return true;
      });
    }

    /*
     * Ordena lexicogràficament un array de 2 dimensions
     * Per exemple:
     *  arr = {{1,0}, {2,2}, {0,1}}
     *  resultat = {{0,1}, {1,0}, {2,2}}
     */
    static int[][] lexSorted(int[][] arr) {
      if (arr == null)
        return null;

      var arr2 = Arrays.copyOf(arr, arr.length);
      Arrays.sort(arr2, Arrays::compare);
      return arr2;
    }

    /*
     * Genera un array int[][] amb els elements {a, b} (a de as, b de bs) que satisfàn pred.test(a, b)
     * Per exemple:
     *   as = {0, 1}
     *   bs = {0, 1, 2}
     *   pred = (a, b) -> a == b
     *   resultat = {{0,0}, {1,1}}
     */
    static int[][] generateRel(int[] as, int[] bs, BiPredicate<Integer, Integer> pred) {
      var rel = new ArrayList<int[]>();

      for (int a : as) {
        for (int b : bs) {
          if (pred.test(a, b)) {
            rel.add(new int[] { a, b });
          }
        }
      }

      return rel.toArray(new int[][] {});
    }

    // Especialització de generateRel per as = bs
    static int[][] generateRel(int[] as, BiPredicate<Integer, Integer> pred) {
      return generateRel(as, as, pred);
    }
  }

  /*
   * Aquí teniu els exercicis del Tema 3 (Grafs).
   *
   * Els (di)grafs vendran donats com llistes d'adjacència (és a dir, tractau-los com diccionaris
   * d'adjacència on l'índex és la clau i els vèrtexos estan numerats de 0 a n-1). Per exemple,
   * podem donar el graf cicle no dirigit d'ordre 3 com:
   *
   * int[][] c3dict = {
   *   {1, 2}, // veïns de 0
   *   {0, 2}, // veïns de 1
   *   {0, 1}  // veïns de 2
   * };
   */
  static class Tema3 {
    /*
     * Determinau si el graf `g` (no dirigit) té cicles.
     */
    static boolean exercici1(int[][] g) {
        boolean[] visitat = new boolean[g.length];
        for (int u = 0; u < g.length; u++) {
            if (!visitat[u]) {
                if (cercaCicle(u, -1, visitat, g)) return true;
            }
        }
        return false;
    }
    private static boolean cercaCicle(int u, int pare, boolean[] visitat, int[][] g) {
        visitat[u] = true;
        for (int v : g[u]) {
            if (!visitat[v]) {
                if (cercaCicle(v, u, visitat, g)) return true;
            } else if (v != pare) {
                // hem trobat un veí visitat que no és el pare, doncs es cicle
                return true;
            }
        }
        return false;
    }

    /*
     * Determinau si els dos grafs són isomorfs. Podeu suposar que cap dels dos té ordre major que
     * 10.
     */
    static boolean exercici2(int[][] g1, int[][] g2) {
        int n = g1.length;
        if (n != g2.length) return false;
        // 1) calcular graus de cada vèrtex
        int[] grau1 = new int[n], grau2 = new int[n];
        for (int i = 0; i < n; i++) {
            grau1[i] = g1[i].length;
            grau2[i] = g2[i].length;
        }
        // 2) crear ordre per graus creixents
        Integer[] ordre = new Integer[n];
        for (int i = 0; i < n; i++) ordre[i] = i;
        Arrays.sort(ordre, (u, v) -> Integer.compare(grau1[u], grau1[v]));
        // 3) recerca per permutacions vàlides
        boolean[] usat = new boolean[n];
        int[] permutacio = new int[n];
        return recercaPermutacions(0, n, ordre, grau1, grau2, permutacio, usat, g1, g2);
    }

    private static boolean recercaPermutacions(int idx, int n, Integer[] ordre,
                                               int[] grau1, int[] grau2,
                                               int[] permutacio, boolean[] usat,
                                               int[][] g1, int[][] g2) {
        if (idx == n) {
            // comprovar que cada aresta de g1 existeix en g2 permutada
            for (int u = 0; u < n; u++) {
                int uu = permutacio[u];
                for (int v : g1[u]) {
                    int vv = permutacio[v];
                    boolean trobat = false;
                    for (int x : g2[uu]) {
                        if (x == vv) { trobat = true; break; }
                    }
                    if (!trobat) return false;
                }
            }
            return true;
        }
        int u = ordre[idx];
        for (int v = 0; v < n; v++) {
            if (!usat[v] && grau1[u] == grau2[v]) {
                usat[v] = true;
                permutacio[u] = v;
                if (recercaPermutacions(idx + 1, n, ordre, grau1, grau2, permutacio, usat, g1, g2))
                    return true;
                usat[v] = false;
            }
        }
        return false;
    }

    /*
     * Determinau si el graf `g` (no dirigit) és un arbre. Si ho és, retornau el seu recorregut en
     * postordre desde el vèrtex `r`. Sinó, retornau null;
     *
     * En cas de ser un arbre, assumiu que l'ordre dels fills vé donat per l'array de veïns de cada
     * vèrtex.
     */
    static int[] exercici3(int[][] g, int r) {
        int n = g.length;
        //comprovar n-1 arestes
        int edgeCount = 0;
        for (int u = 0; u < n; u++) {
            edgeCount += g[u].length;
        }
        edgeCount /= 2;
        if (edgeCount != n - 1) return null;
        // comprovar connexitat i absència de cicles
        boolean[] visited = new boolean[n];
        if (detectaCicleIComponentsDesconexes(r, -1, g, visited)) return null;
        for (boolean vis : visited) {
            if (!vis) return null;
        }
        // recórrer en postordre
        List<Integer> ordre = new ArrayList<>();
        recorregutPostordre(r, -1, g, ordre);
        int[] resultat = new int[ordre.size()];
        for (int i = 0; i < ordre.size(); i++) {
            resultat[i] = ordre.get(i);
        }
        return resultat;
    }
    private static boolean detectaCicleIComponentsDesconexes(int u, int parent, int[][] g, boolean[] visited) {
        visited[u] = true;
        for (int v : g[u]) {
            if (!visited[v]) {
                if (detectaCicleIComponentsDesconexes(v, u, g, visited)) return true;
            } else if (v != parent) {
                // hem detectat un cicle
                return true;
            }
        }
        return false;
    }
    private static void recorregutPostordre(int u, int parent, int[][] g, List<Integer> ordre) {
        for (int v : g[u]) {
            if (v == parent) continue;
            recorregutPostordre(v, u, g, ordre);
        }
        ordre.add(u);
    }
      // Omple 'order' amb el recorregut en postordre del subarbre que té arrel a `u`
    private static void postOrder(int u, int parent, int[][] g, List<Integer> order) {
        for (int v : g[u]) {
          if (v == parent) continue;
          postOrder(v, u, g, order);
        }
        order.add(u);
      }

    /*
     * Suposau que l'entrada és un mapa com el següent, donat com String per files (vegeu els tests)
     *
     *   _____________________________________
     *  |          #       #########      ####|
     *  |       O  # ###   #########  ##  ####|
     *  |    ####### ###   #########  ##      |
     *  |    ####  # ###   #########  ######  |
     *  |    ####    ###              ######  |
     *  |    ######################## ##      |
     *  |    ####                     ## D    |
     *  |_____________________________##______|
     *
     * Els límits del mapa els podeu considerar com els límits de l'array/String, no fa falta que
     * cerqueu els caràcters "_" i "|", i a més podeu suposar que el mapa és rectangular.
     *
     * Donau el nombre mínim de caselles que s'han de recorrer per anar de l'origen "O" fins al
     * destí "D" amb les següents regles:
     *  - No es pot sortir dels límits del mapa
     *  - No es pot passar per caselles "#"
     *  - No es pot anar en diagonal
     *
     * Si és impossible, retornau -1.
     */
    static int exercici4(char[][] mapa) {
        int n = mapa.length;
        int m = mapa[0].length;
        // Troba l'origen
        int sr = -1, sc = -1;
        for (int i = 0; i < n; i++) {
          for (int j = 0; j < m; j++) {
            if (mapa[i][j] == 'O') {
              sr = i; sc = j;
              break;
            }
          }
          if (sr != -1) break;
        }
  
        boolean[][] vis = new boolean[n][m];
        java.util.Queue<int[]> q = new java.util.LinkedList<>();
        q.add(new int[]{sr, sc, 0});
        vis[sr][sc] = true;
        int[][] dirs = {{1,0},{-1,0},{0,1},{0,-1}};
        while (!q.isEmpty()) {
          int[] cur = q.poll();
          int r = cur[0], c = cur[1], d = cur[2];
          // si som a la destinació
          if (mapa[r][c] == 'D') return d;
          // explora veïns
          for (int[] dir : dirs) {
            int nr = r + dir[0], nc = c + dir[1];
            if (nr < 0 || nr >= n || nc < 0 || nc >= m) continue;
            if (vis[nr][nc] || mapa[nr][nc] == '#') continue;
            vis[nr][nc] = true;
            q.add(new int[]{nr, nc, d + 1});
          }
        }
        // no s'ha arribat a D
        return -1;
    }

    /*
     * Aquí teniu alguns exemples i proves relacionades amb aquests exercicis (vegeu `main`)
     */
    static void tests() {

      final int[][] D2 = { {}, {} };
      final int[][] C3 = { {1, 2}, {0, 2}, {0, 1} };

      final int[][] T1 = { {1, 2}, {0}, {0} };
      final int[][] T2 = { {1}, {0, 2}, {1} };

      // Exercici 1
      // G té cicles?

      test(3, 1, 1, () -> !exercici1(D2));
      test(3, 1, 2, () -> exercici1(C3));

      // Exercici 2
      // Isomorfisme de grafs

      test(3, 2, 1, () -> exercici2(T1, T2));
      test(3, 2, 2, () -> !exercici2(T1, C3));

      // Exercici 3
      // Postordre

      test(3, 3, 1, () -> exercici3(C3, 1) == null);
      test(3, 3, 2, () -> Arrays.equals(exercici3(T1, 0), new int[] { 1, 2, 0 }));

      // Exercici 4
      // Laberint

      test(3, 4, 1, () -> {
        return -1 == exercici4(new char[][] {
            " #O".toCharArray(),
            "D# ".toCharArray(),
            " # ".toCharArray(),
        });
      });

      test(3, 4, 2, () -> {
        return 8 == exercici4(new char[][] {
            "###D".toCharArray(),
            "O # ".toCharArray(),
            " ## ".toCharArray(),
            "    ".toCharArray(),
        });
      });
    }
  }

  /*
   * Aquí teniu els exercicis del Tema 4 (Aritmètica).
   *
   * En aquest tema no podeu:
   *  - Utilitzar la força bruta per resoldre equacions: és a dir, provar tots els nombres de 0 a n
   *    fins trobar el que funcioni.
   *  - Utilitzar long, float ni double.
   *
   * Si implementau algun dels exercicis així, tendreu un 0 d'aquell exercici.
   */
  static class Tema4 {
    /*
     * Primer, codificau el missatge en blocs de longitud 2 amb codificació ASCII. Després encriptau
     * el missatge utilitzant xifrat RSA amb la clau pública donada.
     *
     * Per obtenir els codis ASCII del String podeu utilitzar `msg.getBytes()`.
     *
     * Podeu suposar que:
     * - La longitud de `msg` és múltiple de 2
     * - El valor de tots els caràcters de `msg` està entre 32 i 127.
     * - La clau pública (n, e) és de la forma vista a les transparències.
     * - n és major que 2¹⁴, i n² és menor que Integer.MAX_VALUE
     *
     * Pista: https://en.wikipedia.org/wiki/Exponentiation_by_squaring
     */
    static int[] exercici1(String msg, int n, int e) {
        // Convertim el missatge a un array de bytes ASCII
        byte[] ascii = msg.getBytes();
        int numBlocks = ascii.length / 2;
        int[] encrypted = new int[numBlocks];

        // Cada bloc de 2 bytes es codifica com b0*128 + b1
        for (int i = 0; i < numBlocks; i++) {
            int high = ascii[2*i] & 0x7F;
            int low  = ascii[2*i + 1] & 0x7F;
            int block = high * 128 + low;
            // Encriptació modular per exponentiation by squaring
            encrypted[i] = modPow(block, e, n);
        }
        return encrypted;
    }

    /*
     * Primer, desencriptau el missatge utilitzant xifrat RSA amb la clau pública donada. Després
     * descodificau el missatge en blocs de longitud 2 amb codificació ASCII (igual que l'exercici
     * anterior, però al revés).
     *
     * Per construir un String a partir d'un array de bytes podeu fer servir el constructor
     * `new String(byte[])`. Si heu de factoritzar algun nombre, ho podeu fer per força bruta.
     *
     * També podeu suposar que:
     * - La longitud del missatge original és múltiple de 2
     * - El valor de tots els caràcters originals estava entre 32 i 127.
     * - La clau pública (n, e) és de la forma vista a les transparències.
     * - n és major que 2¹⁴, i n² és menor que Integer.MAX_VALUE
     */
    static String exercici2(int[] m, int n, int e) {
        //Factoritzem n = p * q per força bruta
        int p = 0, q = 0;
        for (int i = 2; i * i <= n; i++) {
            if (n % i == 0) {
                p = i;
                q = n / i;
                break;
            }
        }
        if (p == 0) throw new IllegalArgumentException("n no és compost");

        //Calculem φ(n) = (p-1)*(q-1) i després l'invers modular d de e
        int phi = (p - 1) * (q - 1);
        int d   = modInverse(e, phi);

        //Desencriptar cada bloc i reconstruir l'array de bytes
        byte[] resultBytes = new byte[m.length * 2];
        for (int i = 0; i < m.length; i++) {
            int decrypted = modPow(m[i], d, n);
            resultBytes[2*i]     = (byte)(decrypted / 128);
            resultBytes[2*i + 1] = (byte)(decrypted % 128);
        }
        //Convertim els bytes a String i retornem
        return new String(resultBytes);
    }
    // Mètodes auxiliars

    //Potència modular
    private static int modPow(int base, int exp, int mod) {
        int result = 1;
        base %= mod;
        while (exp > 0) {
            if ((exp & 1) == 1) {
                result = (result * base) % mod;
            }
            base = (base * base) % mod;
            exp >>>= 1;
        }
        return result;
    }
    //Euclides estès: retorna [g, x, y] tal que ax+by=g=gcd(a,b)
    private static int[] extendedGcd(int a, int b) {
        if (b == 0) return new int[]{a, 1, 0};
        int[] r = extendedGcd(b, a % b);
        int g = r[0], x = r[2], y = r[1] - (a / b) * r[2];
        return new int[]{g, x, y};
    }
    //Calcula l'invers modular de 'a' mòdul 'm' (suposa gcd(a,m)=1)
    private static int modInverse(int a, int m) {
        int[] r = extendedGcd(a, m);
        if (r[0] != 1) throw new ArithmeticException("No existeix invers modular");
        int inv = r[1] % m;
        return inv < 0 ? inv + m : inv;
    }

    static void tests() {
      // Exercici 1
      // Codificar i encriptar
      test(4, 1, 1, () -> {
        var n = 2*8209;
        var e = 5;

        var encr = exercici1("Patata", n, e);
        return Arrays.equals(encr, new int[] { 4907, 4785, 4785 });
      });

      // Exercici 2
      // Desencriptar i decodificar
      test(4, 2, 1, () -> {
        var n = 2*8209;
        var e = 5;

        var encr = new int[] { 4907, 4785, 4785 };
        var decr = exercici2(encr, n, e);
        return "Patata".equals(decr);
      });
    }
  }

  /*
   * Aquest mètode `main` conté alguns exemples de paràmetres i dels resultats que haurien de donar
   * els exercicis. Podeu utilitzar-los de guia i també en podeu afegir d'altres (no els tendrem en
   * compte, però és molt recomanable).
   *
   * Podeu aprofitar el mètode `test` per comprovar fàcilment que un valor sigui `true`.
   */
  public static void main(String[] args) {
    System.out.println("---- Tema 1 ----");
    Tema1.tests();
    System.out.println("---- Tema 2 ----");
    Tema2.tests();
    System.out.println("---- Tema 3 ----");
    Tema3.tests();
    System.out.println("---- Tema 4 ----");
    Tema4.tests();
  }

  // Informa sobre el resultat de p, juntament amb quin tema, exercici i test es correspon.
  static void test(int tema, int exercici, int test, BooleanSupplier p) {
    try {
      if (p.getAsBoolean())
        System.out.printf("Tema %d, exercici %d, test %d: OK\n", tema, exercici, test);
      else
        System.out.printf("Tema %d, exercici %d, test %d: Error\n", tema, exercici, test);
    } catch (Exception e) {
      if (e instanceof UnsupportedOperationException && "pendent".equals(e.getMessage())) {
        System.out.printf("Tema %d, exercici %d, test %d: Pendent\n", tema, exercici, test);
      } else {
        System.out.printf("Tema %d, exercici %d, test %d: Excepció\n", tema, exercici, test);
        e.printStackTrace();
      }
    }
  }
}

// vim: set textwidth=100 shiftwidth=2 expandtab :
