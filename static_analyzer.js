const esprima = require("esprima");
const options = { tokens: true, tolerant: true, loc: true, range: true };
const fs = require("fs");
const chalk = require('chalk');
const path = require('path')

function main() {
	var args = process.argv.slice(2);
	if (args.length == 0) {
		// default value if no other directory is provided.
		args = ['./'];
	}
	var filePath = args[0];

	let fileList = listFiles(filePath);

	console.log("Parsing ast and running static analysis...");
	var container = [];

	let idx = 0;
	fileList.forEach(file => {
		if (file.endsWith(".js")) {
			container.push({});
			complexity(file, container[idx++]);
		}
	});

	console.log("Complete.\n");

	let allViolations = [];
	for (var component in container) {
		var nodes = container[component];
		for (var builder in nodes) {
			if (nodes[builder].hasOwnProperty("FunctionName")) {
				allViolations = allViolations.concat(nodes[builder].report());
			} else {
				nodes[builder].report();
				if(Object.keys(nodes).length == 1) {
					console.log(chalk`{bgBlue No Function Declaration Nodes Found}\n`);
				}
			}

		}
	}

	if (allViolations.length > 0) {
		console.log(chalk`{bgRed.bold VIOLATIONS}`);
		allViolations.forEach(violation => console.log(violation + "\n"));
		process.exitCode = 1;
	} else {
		console.log(chalk`{bgGreen.bold NO VIOLATIONS FOUND}`);
		process.exitCode = 0;
	}

}

// helper function for listing all files in a directory recursively
// sourced from https://gist.github.com/kethinov/6658166#gistcomment-2934861
function listFiles(dir, list = []) {
	let files = fs.readdirSync(dir);
	for (let file of files) {
		// skipping node_modules
		if (file === "node_modules") {
			continue;
		}
		let stat = fs.statSync(path.join(dir, file));
		if (stat.isDirectory()) {
			list = listFiles(path.join(dir, file), list);
		} else {
			list.push(path.join(dir, file));
		}
	}
	return list;
}

// Helper function for calculating max message chains
function maxChainsHelper(child) {
	let chain = 0, maxChains = 0;
	traverseWithParents(child, function (expression) {
		if (expression.type == "MemberExpression") {
			chain++;
			// since we're not counting indexing, e.g., a[1] as chains
			if (expression.property.type == "Literal") {
				chain--;
			}
		}
		if (expression.type == "FunctionExpression") {
			chain = 0;
		}
		maxChains = Math.max(chain, maxChains);
	});
	return maxChains;
}

function complexity(filePath, builders) {
	var buf = fs.readFileSync(filePath, "utf8");
	var ast = esprima.parse(buf, options);

	// Initialize builder for file-level information
	var fileBuilder = new FileBuilder();
	fileBuilder.FileName = filePath;
	builders[filePath] = fileBuilder;

	// Traverse program with a function visitor.
	traverseWithParents(ast, function (node) {
		// File level calculations
		// 1. Strings
		if (node.type == "Literal" && typeof node.value == "string") {
			fileBuilder.Strings++;
		}

		// 2. Packages
		if (node.type == "CallExpression" && node.callee.type == "Identifier" && node.callee.name == "require") {
			fileBuilder.ImportCount++;
		}

		if (node.type === 'FunctionDeclaration') {
			var builder = new FunctionBuilder();
			builder.FileName = fileBuilder.FileName;
			builder.FunctionName = functionName(node);
			builder.StartLine = node.loc.start.line;
			// Calculate function level properties.
			// 3. Parameters
			builder.ParameterCount = node.params.length;
			// 4. Method Length
			builder.Length = node.loc.end.line - node.loc.start.line;

			// With new visitor(s)...			
			traverseWithParents(node, function (child) {
				if (isDecision(child)) {
					// 5. CyclomaticComplexity
					builder.SimpleCyclomaticComplexity++;

					// 7. Max conditions	
					let conditions = 0;
					if (child.type == "IfStatement") {
						conditions = 1;
						traverseWithParents(child, function (test) {
							if (test.type == "LogicalExpression") {
								conditions++;
							}
						});
					}
					builder.MaxConditions = Math.max(builder.MaxConditions, conditions);
				}

				// 9. Max Message Chains
				if (child.type == "ExpressionStatement") {
					if (child.expression.type == "CallExpression" && child.expression.arguments.length > 0) {
						if (child.expression.arguments[0].type == "FunctionExpression" || child.expression.arguments[0].type == "MemberExpression") {
							builder.MaxMessageChains = Math.max(builder.MaxMessageChains, maxChainsHelper(child.expression.arguments[0]));
						}
					}
					else if (child.expression.type == "MemberExpression" || child.expression.type == "CallExpression") {
						builder.MaxMessageChains = Math.max(builder.MaxMessageChains, maxChainsHelper(child));
					}
				} else if (child.type == "VariableDeclaration") {
					let maxChains = 0;
					child.declarations.forEach(declaration => {
						if (declaration.init != null && (declaration.init.type == "MemberExpression" || declaration.init.type == "CallExpression")) {
							maxChains = Math.max(maxChains, maxChainsHelper(declaration));
						}
					});
					builder.MaxMessageChains = Math.max(builder.MaxMessageChains, maxChains);
				} else if (child.type == "ReturnStatement" && child.argument != null) {
					if (child.argument.type == "CallExpression" && child.argument.arguments.length > 0) {
						if (child.argument.arguments[0].type == "FunctionExpression" || child.argument.arguments[0].type == "MemberExpression") {
							builder.MaxMessageChains = Math.max(builder.MaxMessageChains, maxChainsHelper(child.argument.arguments[0]));
						}
					}
					else if (child.argument.type == "MemberExpression" || child.argument.type == "CallExpression") {
						builder.MaxMessageChains = Math.max(builder.MaxMessageChains, maxChainsHelper(child));
					}
				}
			});

			// 8. Max Nesting Depth
			let current = 0, maxDepth = 0;
			traverseWithParents(node, function (child) {
				if (childrenLength(child) == 0) {
					while (child.type != "FunctionDeclaration") {
						if (isDecision(child) && child.parent.alternate == null) {
							current++;
						}
						child = child.parent;
					}
				}
				maxDepth = Math.max(current, maxDepth);
				current = 0;
			});
			builder.MaxNestingDepth = maxDepth;

			// 6. Halstead
			let set = new Set();
			traverseWithParents(node, function (child) {
				if (child.type == "BinaryExpression" || child.type == "LogicalExpression") {
					set.add(child.operator);
				} else if (child.type == "Identifier") {
					set.add(child.name);
				}
			});
			builder.Halstead = set.size - 1; // -1 to not count function declaration

			builders[builder.FunctionName] = builder;
		}

	});

}

// Represent a reusable "class" following the Builder pattern.
class FunctionBuilder {
	constructor() {
		// Name of the file in which this function exists
		this.FileName = "";
		// Start line position of function
		this.StartLine = 0;
		// Name of the function
		this.FunctionName = "";
		// The number of parameters for functions
		this.ParameterCount = 0;
		// The number of lines.
		this.Length = 0;
		// Number of if statements/loops + 1
		this.SimpleCyclomaticComplexity = 1;
		// Number of unique symbols + operators
		this.Halstead = 0;
		// The max depth of scopes (nested ifs, loops, etc)
		this.MaxNestingDepth = 0;
		// The max number of conditions if one decision statement.
		this.MaxConditions = 0;
		// The max number of message chains in an expression
		this.MaxMessageChains = 0;
	}

	threshold() {

		const thresholds = {
			SimpleCyclomaticComplexity: [{ t: 10, color: 'red' }, { t: 4, color: 'yellow' }],
			Halstead: [{ t: 10, color: 'red' }, { t: 3, color: 'yellow' }],
			ParameterCount: [{ t: 10, color: 'red' }, { t: 3, color: 'yellow' }],
			Length: [{ t: 100, color: 'red' }, { t: 30, color: 'yellow' }],
			MaxNestingDepth: [{ t: 5, color: 'red' }, { t: 3, color: 'yellow' }],
			MaxMessageChains: [{ t: 10, color: 'red' }, { t: 5, color: 'yellow' }]
		}

		const showScore = (id, value) => {
			let scores = thresholds[id];
			const lowestThreshold = { t: 0, color: 'green' };
			const score = scores.sort((a, b) => { a.t - b.t }).find(score => score.t <= value) || lowestThreshold;
			return score.color;
		};

		this.Halstead = chalk`{${showScore('Halstead', this.Halstead)} ${this.Halstead}}`;
		this.ParameterCount = chalk`{${showScore('ParameterCount', this.ParameterCount)} ${this.ParameterCount}}`;
		this.SimpleCyclomaticComplexity = chalk`{${showScore('SimpleCyclomaticComplexity', this.SimpleCyclomaticComplexity)} ${this.SimpleCyclomaticComplexity}}`;

		let violations = [];

		if (this.Length > 100) {
			
			this.Length = chalk`{${showScore('Length', this.Length)} ${this.Length}}`;
			violations.push(chalk`{cyan.underline ${this.FunctionName}}(): at line #${this.StartLine} in ${this.FileName}\nLength: ${this.Length}`);
		} else {
			this.Length = chalk`{${showScore('Length', this.Length)} ${this.Length}}`;
		}

		if (this.MaxNestingDepth > 5) {
			
			this.MaxNestingDepth = chalk`{${showScore('MaxNestingDepth', this.MaxNestingDepth)} ${this.MaxNestingDepth}}`;
			violations.push(chalk`{cyan.underline ${this.FunctionName}}(): at line #${this.StartLine} in ${this.FileName}\nMaxNestingDepth: ${this.MaxNestingDepth}`);
		} else {
			this.MaxNestingDepth = chalk`{${showScore('MaxNestingDepth', this.MaxNestingDepth)} ${this.MaxNestingDepth}}`;
		}

		if (this.MaxMessageChains > 10) {
			this.MaxMessageChains = chalk`{${showScore('MaxMessageChains', this.MaxMessageChains)} ${this.MaxMessageChains}}`;
			violations.push(chalk`{cyan.underline ${this.FunctionName}}(): at line #${this.StartLine} in ${this.FileName}\nMaxMessageChains: ${this.MaxMessageChains}`);
		} else {
			this.MaxMessageChains = chalk`{${showScore('MaxMessageChains', this.MaxMessageChains)} ${this.MaxMessageChains}}`;
		}

		return violations;

	}

	report() {
		let violations = this.threshold();

		console.log(
			chalk`{cyan.underline ${this.FunctionName}}(): at line #${this.StartLine}
Parameters: ${this.ParameterCount}\tLength: ${this.Length}
Cyclomatic: ${this.SimpleCyclomaticComplexity}\tHalstead: ${this.Halstead}
MaxNestingDepth: ${this.MaxNestingDepth}\tMaxConditions: ${this.MaxConditions}
MaxMessageChains: ${this.MaxMessageChains}\n`
		);

		return violations;

	}

}

// A builder for storing file level information.
function FileBuilder() {
	this.FileName = "";
	// Number of strings in a file.
	this.Strings = 0;
	// Number of imports in a file.
	this.ImportCount = 0;

	this.report = function () {
		console.log(chalk`{bgMagenta ${this.FileName}}
{magenta.underline Packages: ${this.ImportCount}
Strings ${this.Strings}}\n`);
	}
}

// A function following the Visitor pattern.
// Annotates nodes with parent objects.
function traverseWithParents(object, visitor) {
	var key, child;

	visitor.call(null, object);

	for (key in object) {
		if (object.hasOwnProperty(key)) {
			child = object[key];
			if (typeof child === 'object' && child !== null && key != 'parent') {
				child.parent = object;
				traverseWithParents(child, visitor);
			}
		}
	}
}

// Helper function for counting children of node.
function childrenLength(node) {
	var key, child;
	var count = 0;
	for (key in node) {
		if (node.hasOwnProperty(key)) {
			child = node[key];
			if (typeof child === 'object' && child !== null && key != 'parent') {
				count++;
			}
		}
	}
	return count;
}


// Helper function for checking if a node is a "decision type node"
function isDecision(node) {
	if (node.type == 'IfStatement' || node.type == 'ForStatement' || node.type == 'WhileStatement' ||
		node.type == 'ForInStatement' || node.type == 'DoWhileStatement') {
		return true;
	}
	return false;
}

// Helper function for printing out function name.
function functionName(node) {
	if (node.id) {
		return node.id.name;
	}
	return "anon function @" + node.loc.start.line;
}

main();
exports.main = main;