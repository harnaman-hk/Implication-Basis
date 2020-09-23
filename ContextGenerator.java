public class ContextGenerator {
    private int[] pattern = null;
       
    public static void main(String[] args) {
        if (args.length !=2) {
            System.out.println("usage: java ContextGenerator n <example-id>");
            System.out.println("example-id =1 corresponds to n pow n rows context");
            System.out.println("example-id =2 corresponds to 3n +1 rows context");
            return;
        } 
        
        int n = Integer.parseInt(args[0]);
        int exampleId = Integer.parseInt(args[1]);
        
        ContextGenerator cg = new ContextGenerator();
        int[][]ar;
        
        switch(exampleId){
            case 1: 
                ar = cg.generateNpowNContext(n);
                printContextFormat(ar);
                break;
            case 2:
                ar = cg.generate3nContext(n);
                printContextFormat(ar);
                break;
            default:
                System.out.println("Example id can be either 1 or 2");
                break;
        }
    }
    
    public int[][] generateNpowNContext(int n) {
        pattern = new int[n];
        int nPowN = (int)Math.pow(n, n);
        
        int[][] ar = new int[nPowN + 1][n * n];
        for (int i = 1; i < ar.length; i++) {
            int tmp = i-1;
            for (int j = 0; j < n ; j++) {
                int patternId = tmp%n;
                int []tmpPattern = generatePattern(patternId, n);
                System.arraycopy(tmpPattern, 0, ar[i], j*n, n);
                tmp = tmp/n;
            }
        }
        return ar;
        
    }
    
    private int[] generatePattern(int patternId, int n) {
        for (int i =0; i<n; i++) {
            pattern[i] = 1;
        }
        pattern[patternId] = 0;
        return pattern;
    }

    public int[][] generate3nContext(int n) {
        int[][] ar = new int[3 * n + 1][2 * n + 1];
        for (int j = 0; j < 2 * n + 1; j++) {
            for (int i = 1; i <= n; i++) {
                if (j != 0 && j != i && j != i + n) {
                    ar[i][j] = 1;
                }
            }
            for (int i = n + 1; i <= 3 * n; i++) {
                if (j != i - n) {
                    ar[i][j] = 1;
                }
            }
        }
        return ar;
    }

    private static void printContextFormat(int[][] ar) {
       // printHumanReadableFormat(ar);
        int rows = ar.length;
        int cols = ar[0].length;
        for (int i = 1; i < rows; i++) {
            for (int j = 0; j < cols; j++) {
                if (ar[i][j] == 1) {
                    System.out.print((j + 1) + " ");
                }
            }
            System.out.println();
        }
    }

    private static void printHumanReadableFormat(int[][] ar) {
        int rows = ar.length;
        int cols = ar[0].length;
        for (int i = 1; i < rows; i++) {
            System.out.println();
            for (int j = 0; j < cols; j++) {
                System.out.print(ar[i][j] + " ");
            }
        }
    }
}

