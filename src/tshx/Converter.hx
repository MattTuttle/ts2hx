package tshx;

import tshx.Ast;
import haxe.macro.Expr;
using StringTools;

typedef HaxeModule = {
	name: String,
	types: Array<TypeDefinition>,
	toplevel: Array<Field>
}

typedef HaxeClass = {
	fields: Array<Field>,
	parent: String
};

class Converter {

	static var nullPos = { min:0, max:0, file:"" };
	static var tDynamic = TPath({ pack: [], name: "Dynamic", sub: null, params: [] });
	static var tInt = { pack: [], name: "Int", sub: null, params: [] };

	var classes:Map<String, HaxeClass>;
	public var modules(default, null):Map<String, HaxeModule>;
	var currentModule:HaxeModule;

	public function new() {
		modules = new Map();
		classes = new Map();
	}

	public function convert(module:TsModule) {
		convertDecl(DModule(module));

		// prevent redefinition of members in subclasses
		// must be done after all classes are converted to resolve forward declarations
		for (className in classes.keys())
		{
			var c = classes.get(className);
			// only do work if the class has a parent
			if (c.parent != null) {
				for (type in currentModule.types)
				{
					if (type.name == className)
					{
						var parentFields = getClassFields(c.parent);
						type.fields =  c.fields.filter(function(field:Field) {
							if (field.name == "new") return true;
							if (parentFields.indexOf(field.name) != -1)
							{
								return false;
							}
							return true;
						});
						break;
					}
				}
			}
		}
	}

	function convertDecl(d:TsDeclaration) {
		switch(d) {
			case DModule(m) | DExternalModule(m):
				convertModule(m);
			case DInterface(i):
				currentModule.types.push(convertInterface(i));
			case DClass(c):
				currentModule.types.push(convertClass(c));
			case DEnum(en):
				currentModule.types.push(convertEnum(en));
			case DTypedef(t):
				// TODO
				trace("Unsupported: " + t);
			case DFunction(sig):
				currentModule.toplevel.push({
					name: sig.name,
					access: [AStatic],
					pos: nullPos,
					kind: FFun(convertFunction(sig.callSignature)),
				});
			case DVariable(v):
				currentModule.toplevel.push({
					name: v.name,
					access: [AStatic],
					pos: nullPos,
					kind: FVar(v.type == null ? tDynamic : convertType(v.type))
				});
			case DImport(_) | DExternalImport(_) | DExportAssignment(_):
				// TODO: do we need these?
		}
	}

	function convertFields(fl:Array<TsTypeMember>) {
		var fields = [];
		var fieldMap = new Map();
		for (mem in fl) {
			var field = convertMember(mem);
			if (field != null) {
				if (fieldMap.exists(field.name)) {
					var field2 = fieldMap[field.name];
					var f = switch(field.kind) {
						case FFun(f):
							f;
						case _:
							// TODO: this probably means we have a member + static property with the same name
							continue;
					}
					f.expr = { expr: EBlock([]), pos: nullPos };
					field2.meta.push({name: ":overload", params: [{expr:EFunction(null, f), pos: nullPos}], pos: nullPos});
				} else {
					fields.push(field);
					fieldMap[field.name] = field;
				}
			}
		}
		return fields;
	}

	function convertModule(m:TsModule) {
		var name = pathToString(m.path);
		if (!modules.exists(name)) {
			modules.set(name, {
				name: name,
				types: [],
				toplevel: []
			});
		}
		var old = currentModule;
		currentModule = modules.get(name);
		for (decl in m.elements) {
			convertDecl(decl);
		}
		if (currentModule.toplevel.length > 0) {
			currentModule.types.push({
				pack: [],
				name: capitalize(name.replace("/", "_")),
				pos: nullPos,
				meta: [nativeMeta(name)],
				isExtern: true,
				kind: TDClass(),
				fields: currentModule.toplevel
			});
		}
	}

	function convertInterface(i:TsInterface) {
		var fields = convertFields(i.t);
		var parents = i.parents.map(convertTypeReference);
		var kind = parents.length == 0 ? TAnonymous(fields) : TExtend(parents, fields);
		var meta = [];
		var name = convertClassName(i.name);
		var path = currentModule.name + "." + i.name;
		if (name != path)
		{
			meta.push(nativeMeta(path));
		}
		var td = {
			pack: [],
			name: name,
			pos: nullPos,
			meta: meta,
			params: i.params.map(convertTypeParameter),
			isExtern: false,
			kind: TDAlias(kind),
			fields: []
		}
		return td;
	}

	function getClassFields(c:String):Array<String> {
		if (!classes.exists(c)) return [];
		var cl = classes.get(c);
		var fields = [for (f in cl.fields) f.name];
		return (cl.parent == null ? fields : fields.concat(getClassFields(cl.parent)));
	}

	function convertClass(c:TsClass) {
		var fields = convertFields(c.t);
		var interfaces = c.interfaces.map(convertTypeReference);
		// TODO: can't implement typedefs, I guess we can rely on structural subtyping
		interfaces = [];
		var meta = [];
		var name = convertClassName(c.name);
		var path = currentModule.name + "." + c.name;
		if (name != path)
		{
			meta.push(nativeMeta(path));
		}
		var parentClass = null;
		if (c.parentClass != null) {
			parentClass = convertTypeReference(c.parentClass);
		}
		classes.set(name, { fields: fields, parent: parentClass == null ? null : parentClass.name });
		return {
			pack: [],
			name: name,
			pos: nullPos,
			meta: meta,
			params: c.params.map(convertTypeParameter),
			isExtern: true,
			kind: TDClass(parentClass, interfaces),
			fields: fields
		};
	}

	function convertEnum(en:TsEnum) {
		var i = 0;
		var fields = en.constructors.map(function(ctor) {
			if (ctor.value != null) {
				// TODO: I guess exported enums should not have int values
				i = Std.parseInt(ctor.value);
			}
			return {
				name: convertPropertyName(ctor.name),
				kind: FVar(null, { expr: EConst(CInt("" +i++)), pos: nullPos }),
				doc: null,
				meta: [],
				access: [],
				pos: nullPos
			}
		});
		var meta = [{name: ":enum", params: [], pos: nullPos}];
		var name = convertClassName(en.name);
		var path = currentModule.name + "." + en.name;
		if (name != path)
		{
			meta.push(nativeMeta(path));
		}
		var td = {
			pack: [],
			name: name,
			pos: nullPos,
			meta: meta,
			params: [],
			isExtern: false,
			kind: TDAbstract(TPath(tInt)),
			fields: fields
		}
		return td;
	}

	function convertMember(mem:TsTypeMember) {
		var o = switch(mem) {
			case TProperty(sig):
				var kind = FVar(sig.type == null ? tDynamic : convertType(sig.type));
				{ kind: kind, name: sig.name, opt: sig.optional, access: if (sig.isStatic) [AStatic] else [] };
			case TMethod(sig):
				switch (sig.name) {
					case TIdentifier("constructor"):
						sig.callSignature.type = TPredefined(TVoid);
						sig.name = TIdentifier("new");
					default:
				}
				var kind = FFun(convertFunction(sig.callSignature));
				{ kind: kind, name: sig.name, opt: sig.optional, access: if (sig.isStatic) [AStatic] else [] };
			case TCall(_) | TConstruct(_) | TIndex(_):
				return null;
		}
		var meta = [];
		if (o.opt) meta.push({name: ":optional", params: [], pos: nullPos});
		// check if converted property name matches the original, if not add @:native metadata
		var name = convertPropertyName(o.name);
		var original = originalPropertyName(o.name);
		if (name != original) meta.push(nativeMeta(original));

		return { name: name, kind: o.kind, doc: null, meta: meta, access: o.access, pos: nullPos };
	}

	function convertFunction(sig:TsCallSignature):Function
		return {
			args: sig.arguments.map(convertArgument),
			ret: sig.type == null ? tDynamic : convertType(sig.type),
			expr: null,
			params: sig.params.map(convertTypeParameter)
		};

	function convertArgument(arg:TsArgument) {
		return {
			name: arg.name,
			opt: arg.optional,
			type: arg.type == null ? tDynamic : convertType(arg.type),
			value: null
		}
	}

	function convertTypeParameter(tp:TsTypeParameter) {
		return {
			name: tp.name,
			constraints: tp.constraint == null ? [] : [convertType(tp.constraint)],
			params: []
		}
	}

	function convertType(t:TsType):ComplexType {
		return switch(t) {
			case TPredefined(t):
				TPath(switch(t) {
					case TAny: { name: "Dynamic", pack: [], params: [], sub: null };
					case TNumber: { name: "Float", pack: [], params: [], sub: null };
					case TBoolean: { name: "Bool", pack: [], params: [], sub: null };
					case TString: { name: "String", pack: [], params: [], sub: null };
					case TVoid: { name: "Void", pack: [], params: [], sub: null };
				});
			case TTypeReference(t):
				TPath(convertTypeReference(t));
			case TTypeQuery(path):
				// TODO
				tDynamic;
			case TRestArgument(t):
				TPath({ name: "Rest", pack: ["haxe", "extern"], params: [TPType(convertType(t))] });
			case TTypeLiteral(t):
				switch(t) {
					case TObject(o):
						var fields:Array<Field> = convertFields(o);
						TAnonymous(fields.filter(function(v) return v != null));
					case TArray(t):
						TPath({ name: "Array", pack: [], params: [TPType(convertType(t))], sub: null});
					case TFunction(f):
						var args = f.arguments.map(function(arg) {
							var t = arg.type == null ? tDynamic : convertType(arg.type);
							return arg.optional ? TOptional(t) : t;
						});
						TFunction(args, convertType(f.ret));
					case TConstructor(_):
						// TODO
						tDynamic;
				}
			case TTypeChoice(t1, t2):
				TPath({ name: "EitherType", pack: ["haxe", "extern"], params:[TPType(convertType(t1)), TPType(convertType(t2))], sub: null});
			case TTuple(tl):
				// TODO check if all types in a tuple are the same
				// TODO make an abstract for typed tuples?
				TPath({ name: "Array", pack: [], params: [TPType(TPath({ name: "Dynamic", pack: [], params: [], sub: null }))], sub: null});
		}
	}

	function convertTypeReference(tref:TsTypeReference) {
		var tPath = {
			name: capitalize(tref.path[tref.path.length - 1]),
			pack: tref.path.slice(0, -1),
			params: tref.params.map(function(t) return TPType(convertType(t))),
			sub: null
		};
		// convert types starting with HTML to the js.html package
		var html = ~/^HTML([a-zA-Z]*)$/;
		if (html.match(tPath.name)) {
			tPath.name = "js.html." + html.matched(1);
		}
		switch [tPath.name, tPath.pack] {
			case ["Object", []]:
				tPath.name = "Dynamic";
			case ["RegExp", []]:
				tPath.pack = ["js"];
			case ["Function", []]:
				tPath.pack = ["haxe"];
				tPath.name = "Constraints";
				tPath.sub = "Function";
			case _:
		}
		return tPath;
	}

	function originalPropertyName(pn:TsPropertyName) {
		return switch(pn) {
			case TIdentifier(s): s;
			case TStringLiteral(s): s;
			case TNumericLiteral(s): s;
		}
	}

	function convertPropertyName(pn:TsPropertyName) {
		return switch(pn) {
			case TIdentifier(s): keywords.match(s) ? s + "_" : s;
			case TStringLiteral(s): s;
			case TNumericLiteral(s): "_" + s;
		}
	}

	function pathToString(p:TsIdentifierPath) {
		return p.join(".");
	}

	function nativeMeta(name:String) {
		return { name: ":native", params: [{ expr: EConst(CString(name)), pos: nullPos }], pos: nullPos };
	}

	public function convertClassName(s:String) {
		return capitalize(topLevelClass.match(s) ? s + "_" : s);
	}

	static public function capitalize(s:String) {
		return s.charAt(0).toUpperCase() + s.substr(1);
	}

	static public var keywords = ~/^(break|callback|case|cast|catch|class|continue|default|do|dynamic|else|enum|extends|extern|false|for|function|if|implements|import|in|inline|interface|never|null|override|package|private|public|return|static|super|switch|this|throw|trace|true|try|typedef|untyped|using|var|while)$/;
	static public var topLevelClass = ~/^(Array|ArrayAccess|Bool|Class|Date|DateTools|Dynamic|EReg|Enum|EnumValue|Float|IMap|Int|IntIterator|Iterable|Iterator|Lambda|List|Map|Math|Null|Reflect|Single|Std|String|StringBuf|StringTools|Sys|Type|UInt|ValueType|Void|Xml)$/;
}
