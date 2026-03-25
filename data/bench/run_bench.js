import { readdir, readFile, writeFile, cp } from 'node:fs/promises';
import { exec } from 'node:child_process';


function execAsync(cmd) {
    return new Promise((resolve, reject) => {
        exec(cmd, (err, stdout, stderr) => {
            if (err) return reject(err);
            return resolve(stdout);
        });
    })
}

async function runBench() {
    const tests = (await readdir('./data/bench/subtyping', { withFileTypes: true }))
        .filter((s) => s.isDirectory())
        .map((s) => s.name);

    for (const test of tests) {
        console.log('Running test case:', test);

        const [gen, raw] = await Promise.all([
            (async () => {
                await cp(
                    `./data/bench/subtyping/${test}/axioms_pre.ml`,
                    './data/predefined/axioms_bench.ml'
                );

                const out = await execAsync(`dune exec ./bin/main.exe subtype-check ./data/bench/subtyping/${test}/test.ml`);
                console.log(out.split('\n').at(-2)); // Assert that this is `result: false`

                return readFile('/tmp/query.v', 'utf-8');
            })(),
            readFile(`./data/bench/subtyping/${test}/mod.json`)
        ]);

        // Simulate an "ideal user" by adding the proofs to the Rocq file programmatically;
        // the Rocq file should now compile.
        const conf = JSON.parse(raw);
        const proven = gen
            .replace('End Signatures.', conf.axioms.map(s => '  ' + s).join('\n') + '\nEnd Signatures.')
            .replace('End Axioms.', conf.axiom_proofs.map(s => s.map(l => '  ' + l).join('\n')).join('\n\n') + '\nEnd Axioms.')
            .replace('    (* ... *)', conf.proof.map(s => '    ' + s).join('\n'))

        // console.log(proven)
        await writeFile(`./data/bench/subtyping/${test}/query.v`, proven);
        await execAsync(`rocq c ./data/bench/subtyping/${test}/query.v`);

        // Convert new axioms back to OCaml syntax
        const out = await execAsync(`cd ../rocqconv && dune exec ./bin/main.exe ../CoverageType/data/bench/subtyping/${test}/query.v`);
        console.log(out);
    }
}

runBench();
