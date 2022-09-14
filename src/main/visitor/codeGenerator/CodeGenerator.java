package main.visitor.codeGenerator;

import classfileanalyzer.Main;
import main.ast.nodes.Program;
import main.ast.nodes.declaration.classDec.ClassDeclaration;
import main.ast.nodes.declaration.classDec.classMembersDec.ConstructorDeclaration;
import main.ast.nodes.declaration.classDec.classMembersDec.FieldDeclaration;
import main.ast.nodes.declaration.classDec.classMembersDec.MethodDeclaration;
import main.ast.nodes.declaration.variableDec.VarDeclaration;
import main.ast.nodes.expression.*;
import main.ast.nodes.expression.operators.BinaryOperator;
import main.ast.nodes.expression.operators.UnaryOperator;
import main.ast.nodes.expression.values.ListValue;
import main.ast.nodes.expression.values.NullValue;
import main.ast.nodes.expression.values.primitive.BoolValue;
import main.ast.nodes.expression.values.primitive.IntValue;
import main.ast.nodes.expression.values.primitive.StringValue;
import main.ast.nodes.statement.*;
import main.ast.nodes.statement.loop.BreakStmt;
import main.ast.nodes.statement.loop.ContinueStmt;
import main.ast.nodes.statement.loop.ForStmt;
import main.ast.nodes.statement.loop.ForeachStmt;
import main.ast.types.NullType;
import main.ast.types.Type;
import main.ast.types.functionPointer.FptrType;
import main.ast.types.list.ListNameType;
import main.ast.types.list.ListType;
import main.ast.types.single.BoolType;
import main.ast.types.single.ClassType;
import main.ast.types.single.IntType;
import main.ast.types.single.StringType;
import main.symbolTable.SymbolTable;
import main.symbolTable.exceptions.ItemNotFoundException;
import main.symbolTable.items.ClassSymbolTableItem;
import main.symbolTable.items.FieldSymbolTableItem;
import main.symbolTable.utils.graph.Graph;
import main.symbolTable.utils.graph.exceptions.GraphDoesNotContainNodeException;
import main.visitor.Visitor;
import main.visitor.typeChecker.ExpressionTypeChecker;

import java.io.*;
import java.util.ArrayList;
import java.util.Stack;

public class CodeGenerator extends Visitor<String> {
    ExpressionTypeChecker expressionTypeChecker;
    Graph<String> classHierarchy;
    private String outputPath;
    private FileWriter currentFile;
    private ClassDeclaration currentClass;
    private MethodDeclaration currentMethod;
    private int labelCounter;
    private int tempVars;

    private Stack<String> brkLabels;
    private Stack<String> cntuLabels;

    public CodeGenerator(Graph<String> classHierarchy) {
        this.classHierarchy = classHierarchy;
        this.expressionTypeChecker = new ExpressionTypeChecker(classHierarchy);
        this.prepareOutputFolder();
        resetParameters();
        this.brkLabels = new Stack<>();
        this.cntuLabels = new Stack<>();
    }

    private String getExpectedType(Type t) {
        String type = null;
        if (t instanceof IntType)
            type = "java/lang/Integer";
        if (t instanceof BoolType)
            type = "java/lang/Boolean";
        if (t instanceof StringType)
            type = "java/lang/String";
        if (t instanceof FptrType)
            type = "Fptr";
        if (t instanceof ListType)
            type = "List";
        if (t instanceof ClassType)
            type = ((ClassType) t).getClassName().getName();
        if (t instanceof NullType)
            type = "V";

        return type;
    }

    private String getFreshLabel() {
        return "LABEL_" + (labelCounter++);
    }

    private String getPrimitiveToClassCmd(Type t) {
        String castCmd = null;
        if (t instanceof IntType)
            castCmd = "invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;";
        if (t instanceof BoolType)
            castCmd = "invokestatic java/lang/Boolean/valueOf(Z)Ljava/lang/Boolean;";

        return castCmd;
    }

    private String getClassToPrimitiveCmd(Type t) {
        String castCmd = null;
        if (t instanceof IntType)
            castCmd = "invokevirtual java/lang/Integer/intValue()I";
        else if (t instanceof BoolType)
            castCmd = "invokevirtual java/lang/Boolean/booleanValue()Z";

        return castCmd;
    }

    private void prepareOutputFolder() {
        this.outputPath = "output/";
        String jasminPath = "utilities/jarFiles/jasmin.jar";
        String listClassPath = "utilities/codeGenerationUtilityClasses/List.j";
        String fptrClassPath = "utilities/codeGenerationUtilityClasses/Fptr.j";
        try{
            File directory = new File(this.outputPath);
            File[] files = directory.listFiles();
            if(files != null)
                for (File file : files)
                    file.delete();
            directory.mkdir();
        }
        catch(SecurityException e) { }
        copyFile(jasminPath, this.outputPath + "jasmin.jar");
        copyFile(listClassPath, this.outputPath + "List.j");
        copyFile(fptrClassPath, this.outputPath + "Fptr.j");
    }

    private void copyFile(String toBeCopied, String toBePasted) {
        try {
            File readingFile = new File(toBeCopied);
            File writingFile = new File(toBePasted);
            InputStream readingFileStream = new FileInputStream(readingFile);
            OutputStream writingFileStream = new FileOutputStream(writingFile);
            byte[] buffer = new byte[1024];
            int readLength;
            while ((readLength = readingFileStream.read(buffer)) > 0)
                writingFileStream.write(buffer, 0, readLength);
            readingFileStream.close();
            writingFileStream.close();
        } catch (IOException e) { }
    }

    private void createFile(String name) {
        try {
            String path = this.outputPath + name + ".j";
            File file = new File(path);
            file.createNewFile();
            FileWriter fileWriter = new FileWriter(path);
            this.currentFile = fileWriter;
        } catch (IOException e) {}
    }

    private void addCommand(String command) {
        try {
            command = String.join("\n\t\t", command.split("\n"));
            if(command.startsWith("Label_"))
                this.currentFile.write("\t" + command + "\n");
            else if(command.startsWith("."))
                this.currentFile.write(command + "\n");
            else
                this.currentFile.write("\t\t" + command + "\n");
            this.currentFile.flush();
        } catch (IOException e) {}
    }

    private void addPrimaryValueCmd(Type t) {
        if (t instanceof IntType) {
            addCommand("ldc 0");
            addCommand("invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;");
        }
        if (t instanceof BoolType) {
            addCommand("ldc 0");
            addCommand("invokestatic java/lang/Boolean/valueOf(Z)Ljava/lang/Boolean;");
        }
        if (t instanceof StringType) {
            addCommand("ldc \"\"");
        }
        if (t instanceof ListType) {
            ListType listType = (ListType) t;
            addCommand("new List\n" +
                    "dup\n" +
                    "new java/util/ArrayList\n" +
                    "dup\n" +
                    "invokespecial java/util/ArrayList/<init>()V");
            for (ListNameType member : listType.getElementsTypes()) {
                addCommand("dup\n");
                addPrimaryValueCmd(member.getType());
                addCommand("invokevirtual java/util/ArrayList/add(Ljava/lang/Object;)Z\n" +
                        "pop");
            }
            addCommand("invokespecial List/<init>(Ljava/util/ArrayList;)V");
        }
        if (t instanceof FptrType) {
            addCommand("aconst_null");
        }
        if (t instanceof ClassType) {
            addCommand("aconst_null");
        }
    }

    private String makeTypeSignature(Type t) {
        String signature = null;
        if (t instanceof IntType)
            signature = "Ljava/lang/Integer;";
        if (t instanceof BoolType)
            signature = "Ljava/lang/Boolean;";
        if (t instanceof StringType)
            signature = "Ljava/lang/String;";
        if (t instanceof FptrType)
            signature = "LFptr;";
        if (t instanceof ListType)
            signature = "LList;";
        if (t instanceof ClassType)
            signature = "L" + ((ClassType) t).getClassName().getName() + ";";
        if (t instanceof NullType)
            signature = "V";

        return signature;
    }

    private void resetParameters() {
        labelCounter = 0;
        tempVars = -1;
    }

    private void addDefaultConstructor() {
        addCommand(".method public <init>()V\n" +
                ".limit stack 128\n" +
                ".limit locals 128\n" +
                "aload_0");

        String invokeCmd = "invokespecial ";
        if (currentClass.getParentClassName() != null)
            invokeCmd += currentClass.getParentClassName().getName();
        else
            invokeCmd += "java/lang/Object";

        invokeCmd += "/<init>()V";
        addCommand(invokeCmd);

        for (FieldDeclaration field : currentClass.getFields()){
            String fieldName = field.getVarDeclaration().getVarName().getName();
            Type fieldType = field.getVarDeclaration().getType();

            addCommand("aload_0");
            addPrimaryValueCmd(fieldType);
            addCommand("putfield " + currentClass.getClassName().getName()
                    + "/" + fieldName + " " + makeTypeSignature(fieldType));
        }
        addCommand("return\n" +
                ".end method");
    }

    private void addStaticMainMethod() {
        addCommand(".method public static main([Ljava/lang/String;)V\n" +
                ".limit stack 128\n" +
                ".limit locals 128\n" +
                "new Main\n" +
                "invokespecial Main/<init>()V\n" +
                "return\n" +
                ".end method");
    }

    private int slotOf(String identifier) {
        if (identifier.equals("")) {
            if (tempVars < 0)
                tempVars = currentMethod.getLocalVars().size() + currentMethod.getArgs().size();
            tempVars++;
            return tempVars;
        }

        int result = 1;
        ArrayList<VarDeclaration> args = currentMethod.getArgs();
        for (VarDeclaration arg : args) {
            if (arg.getVarName().getName().equals(identifier))
                return result;
            result++;
        }
        ArrayList<VarDeclaration> localVars = currentMethod.getLocalVars();
        for (VarDeclaration localVar : localVars) {
            if (localVar.getVarName().getName().equals(identifier))
                return result;
            result++;
        }
        return -1;
    }

    @Override
    public String visit(Program program) {
        ArrayList<ClassDeclaration> classes = program.getClasses();
        for (ClassDeclaration sophiaClass : classes) {
            currentClass = sophiaClass;
            expressionTypeChecker.setCurrentClass(sophiaClass);
            sophiaClass.accept(this);
        }
        return null;
    }

    @Override
    public String visit(ClassDeclaration classDeclaration) {
        createFile(classDeclaration.getClassName().getName());
        addCommand(".class public " + classDeclaration.getClassName().getName());
        if (classDeclaration.getParentClassName() == null)
            addCommand(".super java/lang/Object");
        else
            addCommand(".super " + classDeclaration.getParentClassName().getName());

        ArrayList<FieldDeclaration> fields = classDeclaration.getFields();
        ArrayList<MethodDeclaration> methods = classDeclaration.getMethods();
        ConstructorDeclaration constructorDeclaration = classDeclaration.getConstructor();
        for (FieldDeclaration field : fields)
            field.accept(this);

        resetParameters();
        if (constructorDeclaration != null) {
            currentMethod = constructorDeclaration;
            expressionTypeChecker.setCurrentMethod(constructorDeclaration);
            constructorDeclaration.accept(this);
        }
        else
            addDefaultConstructor();

        resetParameters();
        for (MethodDeclaration methodDeclaration : methods) {
            currentMethod = methodDeclaration;
            expressionTypeChecker.setCurrentMethod(methodDeclaration);
            methodDeclaration.accept(this);
        }

        return null;
    }

    @Override
    public String visit(ConstructorDeclaration constructorDeclaration) {
        if (currentClass.getClassName().getName().equals("Main"))
            addStaticMainMethod();

        if (constructorDeclaration.getArgs().size() > 0)
            addDefaultConstructor();

        this.visit((MethodDeclaration) constructorDeclaration);
        return null;
    }

    @Override
    public String visit(MethodDeclaration methodDeclaration) {
        String signature;
        if(methodDeclaration instanceof ConstructorDeclaration)
            signature = ".method public <init>(";
        else
            signature = ".method public " + methodDeclaration.getMethodName().getName() + "(";

        for (VarDeclaration arg : methodDeclaration.getArgs())
            signature += makeTypeSignature(arg.getType());
        signature += ")" + makeTypeSignature(methodDeclaration.getReturnType());
        addCommand(signature);
        addCommand(".limit stack 128");
        addCommand(".limit locals 128");

        if(methodDeclaration instanceof ConstructorDeclaration) {
            addCommand("aload_0");
            String invokeCmd = "invokespecial ";
            if (currentClass.getParentClassName() != null)
                invokeCmd += currentClass.getParentClassName().getName();
            else
                invokeCmd += "java/lang/Object";
            invokeCmd += "/<init>()V";
            addCommand(invokeCmd);

            for (FieldDeclaration fieldDeclaration : currentClass.getFields()){
                addCommand("aload_0");
                String className = currentClass.getClassName().getName();
                String fieldName = fieldDeclaration.getVarDeclaration().getVarName().getName();
                Type fieldType = fieldDeclaration.getVarDeclaration().getType();
                addPrimaryValueCmd(fieldType);
                addCommand("putfield " + className + "/" + fieldName + " " + makeTypeSignature(fieldType));
            }
        }

        for (VarDeclaration var : methodDeclaration.getLocalVars())
            var.accept(this);

        for (Statement s : methodDeclaration.getBody())
            s.accept(this);

        if (!methodDeclaration.getDoesReturn())
            addCommand("return");

        addCommand(".end method");
        return null;
    }

    @Override
    public String visit(FieldDeclaration fieldDeclaration) {
        addCommand(".field " + fieldDeclaration.getVarDeclaration().getVarName().getName()
                + " " + makeTypeSignature(fieldDeclaration.getVarDeclaration().getType()));
        return null;
    }

    @Override
    public String visit(VarDeclaration varDeclaration) {
        addPrimaryValueCmd(varDeclaration.getType());
        addCommand("astore " + slotOf(varDeclaration.getVarName().getName()));
        return null;
    }

    @Override
    public String visit(AssignmentStmt assignmentStmt) {
        BinaryExpression assignmentExpression = new BinaryExpression(assignmentStmt.getlValue(),
                assignmentStmt.getrValue(), BinaryOperator.assign);
        addCommand(assignmentExpression.accept(this));
        addCommand("pop");
        return null;
    }

    @Override
    public String visit(BlockStmt blockStmt) {
        for (Statement statement : blockStmt.getStatements())
            statement.accept(this);
        return null;
    }

    @Override
    public String visit(ConditionalStmt conditionalStmt) {
        addCommand(conditionalStmt.getCondition().accept(this));

        String ELSE = getFreshLabel();
        String AFTER = getFreshLabel();

        addCommand("ifeq " + ELSE);

        conditionalStmt.getThenBody().accept(this);
        addCommand("goto " + AFTER);

        addCommand(ELSE + ":");
        if (conditionalStmt.getElseBody() != null)
            conditionalStmt.getElseBody().accept(this);

        addCommand(AFTER + ":");
        return null;
    }

    @Override
    public String visit(MethodCallStmt methodCallStmt) {
        expressionTypeChecker.setIsInMethodCallStmt(true);
        addCommand(methodCallStmt.getMethodCall().accept(this));
        addCommand("pop");
        expressionTypeChecker.setIsInMethodCallStmt(false);
        return null;
    }

    @Override
    public String visit(PrintStmt print) {
        Type argType = print.getArg().accept(expressionTypeChecker);
        addCommand("getstatic java/lang/System/out Ljava/io/PrintStream;");
        String primitiveType = null;
        if (argType instanceof IntType)
            primitiveType = "I";
        else if (argType instanceof BoolType)
            primitiveType = "Z";
        else if (argType instanceof StringType)
            primitiveType = "Ljava/lang/String;";

        addCommand(print.getArg().accept(this));

        addCommand("invokevirtual java/io/PrintStream/print(" + primitiveType + ")V");
        return null;
    }

    @Override
    public String visit(ReturnStmt returnStmt) {
        Type returnType = returnStmt.getReturnedExpr().accept(expressionTypeChecker);
        if(returnType instanceof NullType)
            addCommand("return");
        else {
            addCommand(returnStmt.getReturnedExpr().accept(this));
            if (returnType instanceof IntType)
                addCommand("invokestatic java/lang/Integer/valueOf(I)Ljava/lang/Integer;");
            if (returnType instanceof BoolType)
                addCommand("invokestatic java/lang/Boolean/valueOf(Z)Ljava/lang/Boolean;");
            addCommand("areturn");
        }
        return null;
    }

    @Override
    public String visit(BreakStmt breakStmt) {
        addCommand("goto " + brkLabels.peek());
        return null;
    }

    @Override
    public String visit(ContinueStmt continueStmt) {
        addCommand("goto " + cntuLabels.peek());
        return null;
    }

    @Override
    public String visit(ForeachStmt foreachStmt) {
        String START = getFreshLabel();
        String CONTINUE = getFreshLabel();
        String BREAK = getFreshLabel();

        cntuLabels.push(CONTINUE);
        brkLabels.push(BREAK);

        ListType listType = (ListType) foreachStmt.getList().accept(expressionTypeChecker);
        int containerSlot = slotOf("");
        int iteratorSlot = slotOf("");
        Type memberType = foreachStmt.getVariable().accept(expressionTypeChecker);

        addCommand("ldc 0\n" +
                "istore " + iteratorSlot);

        addCommand(foreachStmt.getList().accept(this) + "\n" +
                "astore " + containerSlot);

        addCommand(START + ":\n" +
                "iload " + iteratorSlot + "\n" +
                "ldc " + listType.getElementsTypes().size() + "\n" +
                "if_icmpge " + BREAK);

        addCommand("aload " + containerSlot + "\n" +
                "iload " + iteratorSlot + "\n" +
                "invokevirtual List/getElement(I)Ljava/lang/Object;\n" +
                "checkcast " + getExpectedType(memberType) + "\n" +
                "astore " + slotOf(foreachStmt.getVariable().getName()));

        foreachStmt.getBody().accept(this);

        addCommand(CONTINUE + ":\n" +
                "iinc " + iteratorSlot + " 1\n" +
                "goto " + START + "\n" +
                BREAK + ":");

        cntuLabels.pop();
        brkLabels.pop();
        return null;
    }

    @Override
    public String visit(ForStmt forStmt) {
        String START = getFreshLabel();
        String CONTINUE = getFreshLabel();
        String BREAK = getFreshLabel();

        cntuLabels.push(CONTINUE);
        brkLabels.push(BREAK);

        if (forStmt.getInitialize() != null)
            forStmt.getInitialize().accept(this);

        addCommand(START + ":");
        if (forStmt.getCondition() != null) {
            String conditionCmd = forStmt.getCondition().accept(this);
            addCommand(conditionCmd);
            addCommand("ifeq " + BREAK);
        }

        forStmt.getBody().accept(this);

        addCommand(CONTINUE + ":");
        if (forStmt.getUpdate() != null)
            forStmt.getUpdate().accept(this);
        addCommand("goto " + START);

        addCommand(BREAK + ":");

        cntuLabels.pop();
        brkLabels.pop();
        return null;
    }

    @Override
    public String visit(BinaryExpression binaryExpression) {
        BinaryOperator operator = binaryExpression.getBinaryOperator();
        String commands = "";

        commands += binaryExpression.getFirstOperand().accept(this);
        commands += "\n" + binaryExpression.getSecondOperand().accept(this);
        if (operator == BinaryOperator.add) {
            commands += "\niadd";
        }
        else if (operator == BinaryOperator.sub) {
            commands += "\nisub";
        }
        else if (operator == BinaryOperator.mult) {
            commands += "\nimul";
        }
        else if (operator == BinaryOperator.div) {
            commands += "\nidiv";
        }
        else if (operator == BinaryOperator.mod) {
            commands += "\nirem";
        }
        else if((operator == BinaryOperator.gt) || (operator == BinaryOperator.lt)) {
            String TRUE = getFreshLabel();
            String AFTER = getFreshLabel();
            if (operator == BinaryOperator.gt)
                commands += "\nif_icmpgt " + TRUE;
            else
                commands += "\nif_icmplt " + TRUE;
            commands += "\nldc 0" +
                    "\ngoto " + AFTER +
                    "\n" + TRUE + ":" +
                    "\nldc 1" +
                    "\n" + AFTER + ":";
        }
        else if((operator == BinaryOperator.eq) || (operator == BinaryOperator.neq)) {
            String FALSE = getFreshLabel();
            String AFTER = getFreshLabel();

            Type type = binaryExpression.getFirstOperand().accept(expressionTypeChecker);
            if (type instanceof IntType || type instanceof BoolType)
                commands += "\nif_i";
            else
                commands += "\nif_a";

            if (operator == BinaryOperator.eq)
                commands += "cmpne " + FALSE;
            else
                commands += "cmpeq " + FALSE;

            commands += "\nldc 1" +
                    "\ngoto " + AFTER +
                    "\n" + FALSE + ":" +
                    "\nldc 0" +
                    "\n" + AFTER + ":";
        }
        else if(operator == BinaryOperator.and) {
            String TRUE = getFreshLabel();
            String FALSE = getFreshLabel();
            String AFTER = getFreshLabel();

            commands += "\n" + binaryExpression.getFirstOperand().accept(this) +
                    "\nifeq " + FALSE +
                    "\n" + binaryExpression.getSecondOperand().accept(this) +
                    "\nifeq " + FALSE +
                    "\n" + TRUE + ":" +
                    "\nldc 1" +
                    "\ngoto " + AFTER +
                    "\n" + FALSE + ":" +
                    "\nldc 0" +
                    "\n" + AFTER + ":";
        }
        else if(operator == BinaryOperator.or) {
            String TRUE = getFreshLabel();
            String FALSE = getFreshLabel();
            String AFTER = getFreshLabel();

            commands += "\n" + binaryExpression.getFirstOperand().accept(this) +
                    "\nifne " + TRUE +
                    "\n" + binaryExpression.getSecondOperand().accept(this) +
                    "\nifeq " + FALSE +
                    "\n" + TRUE + ":" +
                    "\nldc 1" +
                    "\ngoto " + AFTER +
                    "\n" + FALSE + ":" +
                    "\nldc 0" +
                    "\n" + AFTER + ":";
        }
        else if(operator == BinaryOperator.assign) {
            commands = "";
            Type firstType = binaryExpression.getFirstOperand().accept(expressionTypeChecker);
            Type secondType = binaryExpression.getSecondOperand().accept(expressionTypeChecker);
            String secondOperandCommands = binaryExpression.getSecondOperand().accept(this);
            if(firstType instanceof ListType) {
                secondOperandCommands = "new List\ndup\n" + secondOperandCommands;
                secondOperandCommands += "\n" + "invokespecial List/<init>(LList;)V";
            }
            if(binaryExpression.getFirstOperand() instanceof Identifier) {
                commands += secondOperandCommands +
                        "\ndup";
                String castCmd = getPrimitiveToClassCmd(secondType);
                if (castCmd != null)
                    commands += "\n" + castCmd;
                commands += "\nastore " + slotOf(((Identifier) binaryExpression.getFirstOperand()).getName());
            }
            else if(binaryExpression.getFirstOperand() instanceof ListAccessByIndex) {
                int temp = slotOf("");
                ListAccessByIndex listAccessByIndex = (ListAccessByIndex) binaryExpression.getFirstOperand();
                commands += listAccessByIndex.getInstance().accept(this) +
                        "\ndup" +
                        "\n" + listAccessByIndex.getIndex().accept(this) +
                        "\ndup" +
                        "\nistore " + temp +
                        "\n" + secondOperandCommands;
                String castPrimitiveClassCmd = getPrimitiveToClassCmd(secondType);
                if (castPrimitiveClassCmd != null)
                    commands += "\n" + castPrimitiveClassCmd;
                commands += "\n" + "invokevirtual List/setElement(ILjava/lang/Object;)V" +
                        "\niload " + temp +
                        "\n" + "invokevirtual List/getElement(I)Ljava/lang/Object;" +
                        "\ncheckcast " + getExpectedType(secondType);
                castPrimitiveClassCmd = getClassToPrimitiveCmd(secondType);
                if (castPrimitiveClassCmd != null)
                    commands += "\n" + castPrimitiveClassCmd;
            }
            else if(binaryExpression.getFirstOperand() instanceof ObjectOrListMemberAccess) {
                Expression instance = ((ObjectOrListMemberAccess) binaryExpression.getFirstOperand()).getInstance();
                String memberName = ((ObjectOrListMemberAccess) binaryExpression.getFirstOperand()).getMemberName().getName();
                Type instanceType = instance.accept(expressionTypeChecker);
                if(instanceType instanceof ListType) {
                    int i = 0;
                    ArrayList<ListNameType> elementsTypes = ((ListType) instanceType).getElementsTypes();
                    for (i = 0; i < elementsTypes.size(); i++) {
                        if (memberName.equals(elementsTypes.get(i).getName().getName()))
                            break;
                    }

                    commands += instance.accept(this) +
                            "\ndup" +
                            "\nldc " + i +
                            "\n" + secondOperandCommands;
                    String castPrimitiveClassCmd = getPrimitiveToClassCmd(secondType);
                    if (castPrimitiveClassCmd != null)
                        commands += "\n" + castPrimitiveClassCmd;
                    commands += "\ninvokevirtual List/setElement(ILjava/lang/Object;)V" +
                            "\nldc " + i +
                            "\ninvokevirtual List/getElement(I)Ljava/lang/Object;" +
                            "\ncheckcast " + getExpectedType(secondType);
                    castPrimitiveClassCmd = getClassToPrimitiveCmd(secondType);
                    if (castPrimitiveClassCmd != null)
                        commands += "\n" + castPrimitiveClassCmd;

                }
                else if(instanceType instanceof ClassType) {
                    commands += instance.accept(this) +
                            "\ndup" +
                            "\n" + secondOperandCommands;
                    String castPrimitiveCmd = getPrimitiveToClassCmd(secondType);
                    if (castPrimitiveCmd != null)
                        commands += "\n" + castPrimitiveCmd;
                    String name = ((ClassType) instanceType).getClassName().getName();
                    commands += "\nputfield " + name + "/" + memberName + " " + makeTypeSignature(secondType) +
                            "\ngetfield " + name + "/" + memberName + " " + makeTypeSignature(secondType);
                    castPrimitiveCmd = getClassToPrimitiveCmd(secondType);
                    if (castPrimitiveCmd != null)
                        commands += "\n" + castPrimitiveCmd;
                }
            }
        }
        return commands;
    }

    @Override
    public String visit(UnaryExpression unaryExpression) {
        UnaryOperator operator = unaryExpression.getOperator();
        String commands = "";

        if(operator == UnaryOperator.minus) {
            commands += unaryExpression.getOperand().accept(this) + "\n";
            commands += "ineg";
        }
        else if(operator == UnaryOperator.not) {
            String TRUE = getFreshLabel();
            String AFTER = getFreshLabel();
            commands += unaryExpression.getOperand().accept(this) + "\n";
            commands += "ifne " + TRUE + "\n";
            commands += "ldc 1\n";
            commands += "goto " + AFTER + "\n";
            commands += TRUE + ":\n";
            commands += "ldc 0\n";
            commands += AFTER + ":";
        }
        else if((operator == UnaryOperator.predec) || (operator == UnaryOperator.preinc)) {
            if(unaryExpression.getOperand() instanceof Identifier) {
                commands += unaryExpression.getOperand().accept(this) + "\n";
                commands += "ldc 1\n";
                if (operator == UnaryOperator.preinc)
                    commands += "iadd\n";
                else
                    commands += "isub\n";
                commands += "dup\n";
                commands += getPrimitiveToClassCmd(new IntType()) + "\n";

                commands += "astore " + slotOf(((Identifier) unaryExpression.getOperand()).getName());
            }
            else if(unaryExpression.getOperand() instanceof ListAccessByIndex) {
                commands += ((ListAccessByIndex) unaryExpression.getOperand()).getInstance().accept(this) + "\n";
                commands += ((ListAccessByIndex) unaryExpression.getOperand()).getIndex().accept(this) + "\n";

                commands += unaryExpression.getOperand().accept(this) + "\n";

                commands += "ldc 1\n";
                if (operator == UnaryOperator.preinc)
                    commands += "iadd\n";
                else
                    commands += "isub\n";

                commands += "dup\n";
                commands += getPrimitiveToClassCmd(new IntType()) + "\n";
                int temp = slotOf("");
                commands += "astore " + temp + "\n";

                commands += getPrimitiveToClassCmd(new IntType()) + "\n";

                commands += "invokevirtual List/setElement(ILjava/lang/Object;)V\n";

                commands += "aload " + temp + "\n";
                commands += getClassToPrimitiveCmd(new IntType());
            }
            else if(unaryExpression.getOperand() instanceof ObjectOrListMemberAccess) {
                Expression instance = ((ObjectOrListMemberAccess) unaryExpression.getOperand()).getInstance();
                Type memberType = unaryExpression.getOperand().accept(expressionTypeChecker);
                String memberName = ((ObjectOrListMemberAccess) unaryExpression.getOperand()).getMemberName().getName();
                Type instanceType = instance.accept(expressionTypeChecker);
                if(instanceType instanceof ListType) {
                    commands += instance.accept(this) + "\n";
                    ArrayList<ListNameType> elementsTypes = ((ListType) instanceType).getElementsTypes();
                    int i = 0;
                    for (i = 0; i < elementsTypes.size(); i++){
                        if (memberName.equals(elementsTypes.get(i).getName().getName()))
                            break;
                    }
                    commands += "ldc " + i + "\n";

                    commands += unaryExpression.getOperand().accept(this) + "\n";

                    commands += "ldc 1\n";
                    if (operator == UnaryOperator.preinc)
                        commands += "iadd\n";
                    else
                        commands += "isub\n";

                    commands += "dup\n";
                    commands += getPrimitiveToClassCmd(new IntType()) + "\n";
                    int temp = slotOf("");
                    commands += "astore " + temp + "\n";

                    commands += getPrimitiveToClassCmd(new IntType()) + "\n";

                    commands += "invokevirtual List/setElement(ILjava/lang/Object;)V\n";

                    commands += "aload " + temp + "\n";
                    commands += getClassToPrimitiveCmd(new IntType());
                }
                else if(instanceType instanceof ClassType) {
                    commands += instance.accept(this) + "\n";
                    commands += unaryExpression.getOperand().accept(this) + "\n";

                    commands += "ldc 1\n";
                    if (operator == UnaryOperator.preinc)
                        commands += "iadd\n";
                    else
                        commands += "isub\n";
                    commands += "dup\n";
                    int temp = slotOf("");
                    commands += getPrimitiveToClassCmd(new IntType()) + "\n";
                    commands += "astore " + temp + "\n";

                    commands += getPrimitiveToClassCmd(new IntType()) + "\n";

                    commands += "putfield " + ((ClassType) instanceType).getClassName().getName()
                            + "/" + memberName + " " + makeTypeSignature(new IntType()) + "\n";

                    commands += "aload " + temp + "\n";
                    commands += getClassToPrimitiveCmd(new IntType());
                }
            }
        }
        else if((operator == UnaryOperator.postdec) || (operator == UnaryOperator.postinc)) {
            if(unaryExpression.getOperand() instanceof Identifier) {
                commands += unaryExpression.getOperand().accept(this) + "\n";
                commands += "dup\n";

                commands += "ldc 1\n";
                if (operator == UnaryOperator.postinc)
                    commands += "iadd\n";
                else
                    commands += "isub\n";

                commands += getPrimitiveToClassCmd(new IntType()) + "\n";

                commands += "astore " + slotOf(((Identifier) unaryExpression.getOperand()).getName()) + "\n";
            }
            else if(unaryExpression.getOperand() instanceof ListAccessByIndex) {
                commands += ((ListAccessByIndex) unaryExpression.getOperand()).getInstance().accept(this) + "\n";
                commands += ((ListAccessByIndex) unaryExpression.getOperand()).getIndex().accept(this) + "\n";

                commands += unaryExpression.getOperand().accept(this) + "\n";

                commands += "dup\n";
                int temp = slotOf("");
                commands += getPrimitiveToClassCmd(new IntType()) + "\n";
                commands += "astore " + temp + "\n";

                commands += "ldc 1\n";
                if (operator == UnaryOperator.postinc)
                    commands += "iadd\n";
                else
                    commands += "isub\n";

                commands += getPrimitiveToClassCmd(new IntType()) + "\n";

                commands += "invokevirtual List/setElement(ILjava/lang/Object;)V\n";

                commands += "aload " + temp + "\n";
                commands += getClassToPrimitiveCmd(new IntType());
            }
            else if(unaryExpression.getOperand() instanceof ObjectOrListMemberAccess) {
                Expression instance = ((ObjectOrListMemberAccess) unaryExpression.getOperand()).getInstance();
                Type memberType = unaryExpression.getOperand().accept(expressionTypeChecker);
                String memberName = ((ObjectOrListMemberAccess) unaryExpression.getOperand()).getMemberName().getName();
                Type instanceType = instance.accept(expressionTypeChecker);
                if(instanceType instanceof ListType) {
                    commands += instance.accept(this) + "\n";
                    ArrayList<ListNameType> elementsTypes = ((ListType) instanceType).getElementsTypes();
                    int i = 0;
                    for (i = 0; i < elementsTypes.size(); i++){
                        if (memberName.equals(elementsTypes.get(i).getName().getName()))
                            break;
                    }
                    commands += "ldc " + i + "\n";

                    commands += unaryExpression.getOperand().accept(this) + "\n";
                    commands += "dup\n";
                    int temp = slotOf("");
                    commands += getPrimitiveToClassCmd(new IntType()) + "\n";
                    commands += "astore " + temp + "\n";

                    commands += "ldc 1\n";
                    if (operator == UnaryOperator.postinc)
                        commands += "iadd\n";
                    else
                        commands += "isub\n";

                    commands += getPrimitiveToClassCmd(new IntType()) + "\n";
                    commands += "invokevirtual List/setElement(ILjava/lang/Object;)V\n";
                    commands += "aload " + temp + "\n";
                    commands += getClassToPrimitiveCmd(new IntType());
                }
                else if(instanceType instanceof ClassType) {
                    commands += instance.accept(this) + "\n";
                    commands += unaryExpression.getOperand().accept(this) + "\n";
                    commands += "dup\n";
                    int temp = slotOf("");
                    commands += getPrimitiveToClassCmd(new IntType()) + "\n";
                    commands += "astore " + temp + "\n";


                    commands += "ldc 1\n";
                    if (operator == UnaryOperator.postinc)
                        commands += "iadd\n";
                    else
                        commands += "isub\n";


                    commands += getPrimitiveToClassCmd(new IntType()) + "\n";

                    commands += "putfield " + ((ClassType) instanceType).getClassName().getName()
                            + "/" + memberName + " " + makeTypeSignature(new IntType()) + "\n";
                    commands += "aload " + temp + "\n";
                    commands += getClassToPrimitiveCmd(new IntType());
                }
            }
        }
        return commands;
    }

    @Override
    public String visit(ObjectOrListMemberAccess objectOrListMemberAccess) {
        Type memberType = objectOrListMemberAccess.accept(expressionTypeChecker);
        Type instanceType = objectOrListMemberAccess.getInstance().accept(expressionTypeChecker);
        String memberName = objectOrListMemberAccess.getMemberName().getName();
        String commands = "";
        if(instanceType instanceof ClassType) {
            String className = ((ClassType) instanceType).getClassName().getName();
            try {
                SymbolTable classSymbolTable = ((ClassSymbolTableItem) SymbolTable.root.getItem(ClassSymbolTableItem.START_KEY + className, true)).getClassSymbolTable();
                try {
                    classSymbolTable.getItem(FieldSymbolTableItem.START_KEY + memberName, true);

                    commands += objectOrListMemberAccess.getInstance().accept(this) + "\n" +
                            "getfield " + className + "/" + memberName + " " + makeTypeSignature(memberType) + "\n";
                    String castPrimitiveCmd = getClassToPrimitiveCmd(memberType);
                    if (castPrimitiveCmd != null)
                        commands += castPrimitiveCmd;
                } catch (ItemNotFoundException memberIsMethod) {
                    commands += "new Fptr\n" +
                            "dup\n" +
                            objectOrListMemberAccess.getInstance().accept(this) + "\n" +
                            "ldc \"" + memberName + "\"" + "\n" +
                            "invokespecial Fptr/<init>(Ljava/lang/Object;Ljava/lang/String;)V\n";
                }
            } catch (ItemNotFoundException classNotFound) {
            }
        }
        else if(instanceType instanceof ListType) {
            int i = 0;
            ArrayList<ListNameType> elementTypes = ((ListType) instanceType).getElementsTypes();
            for (i = 0; i < elementTypes.size(); i++){
                if (memberName.equals(elementTypes.get(i).getName().getName()))
                    break;
            }
            commands += objectOrListMemberAccess.getInstance().accept(this) + "\n" +
                    "ldc " + i + "\n" +
                    "invokevirtual List/getElement(I)Ljava/lang/Object;\n" +
                    "checkcast " + getExpectedType(memberType) + "\n";
            String castPrimitiveCmd = getClassToPrimitiveCmd(memberType);
            if (castPrimitiveCmd != null)
                commands += castPrimitiveCmd;
        }
        return commands;
    }

    @Override
    public String visit(Identifier identifier) {
        String commands = "";
        commands += "aload " + slotOf(identifier.getName()) + "\n";
        String castPrimitiveCmd = getClassToPrimitiveCmd(identifier.accept(expressionTypeChecker));
        if (castPrimitiveCmd != null)
            commands += castPrimitiveCmd;
        return commands;
    }

    @Override
    public String visit(ListAccessByIndex listAccessByIndex) {
        String commands = "";
        commands += listAccessByIndex.getInstance().accept(this) + "\n" +
                listAccessByIndex.getIndex().accept(this) + "\n" +
                "invokevirtual List/getElement(I)Ljava/lang/Object;\n";

        commands += "checkcast " + getExpectedType(listAccessByIndex.accept(expressionTypeChecker)) + "\n";

        String castPrimitiveCmd = getClassToPrimitiveCmd(listAccessByIndex.accept(expressionTypeChecker));
        if (castPrimitiveCmd != null)
            commands += castPrimitiveCmd;
        return commands;
    }

    @Override
    public String visit(MethodCall methodCall) {
        String commands = "";
        commands += methodCall.getInstance().accept(this) + "\n" +
                "new java/util/ArrayList\n" +
                "dup\n" +
                "invokespecial java/util/ArrayList/<init>()V\n";
        for (Expression arg : methodCall.getArgs()) {
            commands += "dup\n" +
                    arg.accept(this) + "\n";

            Type type = arg.accept(expressionTypeChecker);
            String castPrimitiveClassCmd = getPrimitiveToClassCmd(type);
            if (castPrimitiveClassCmd != null)
                commands += castPrimitiveClassCmd + "\n";
            commands += "invokevirtual java/util/ArrayList/add(Ljava/lang/Object;)Z\n" +
                    "pop\n";
        }
        commands += "invokevirtual Fptr/invoke(Ljava/util/ArrayList;)Ljava/lang/Object;\n";

        Type returnType = methodCall.accept(expressionTypeChecker);
        if (!(returnType instanceof NullType))
            commands += "checkcast " + getExpectedType(returnType) + "\n";

        String primitiveCastCmd = getClassToPrimitiveCmd(returnType);
        if (primitiveCastCmd != null)
            commands += "\n" + primitiveCastCmd;

        return commands;
    }

    @Override
    public String visit(NewClassInstance newClassInstance) {
        String commands = "";
        commands += "new " + newClassInstance.getClassType().getClassName().getName() + "\n" +
                "dup\n";
        for (Expression arg : newClassInstance.getArgs()) {
            commands += arg.accept(this) + "\n";
            Type type = arg.accept(expressionTypeChecker);
            String castPrimitiveClassCmd = getPrimitiveToClassCmd(type);
            if (castPrimitiveClassCmd != null)
                commands += castPrimitiveClassCmd + "\n";
        }
        commands += "invokespecial " + newClassInstance.getClassType().getClassName().getName() + "/<init>(";
        for (Expression arg : newClassInstance.getArgs()) {
            Type type = arg.accept(expressionTypeChecker);
            commands += makeTypeSignature(type);
        }
        commands += ")V\n";

        return commands;
    }

    @Override
    public String visit(ThisClass thisClass) {
        String commands = "aload_0";
        return commands;
    }

    @Override
    public String visit(ListValue listValue) {
        String commands = "";
        commands += "new List\n" +
                "dup\n" +
                "new java/util/ArrayList\n" +
                "dup\n" +
                "invokespecial java/util/ArrayList/<init>()V\n";
        for (Expression element : listValue.getElements()) {
            Type type = element.accept(expressionTypeChecker);
            commands += "\ndup\n" +
                    element.accept(this) + "\n";
            String castPrimitiveClassCmd = getPrimitiveToClassCmd(type);
            if (castPrimitiveClassCmd != null)
                commands += castPrimitiveClassCmd + "\n";
            commands += "invokevirtual java/util/ArrayList/add(Ljava/lang/Object;)Z\n" +
                    "pop\n";
        }
        commands += "invokespecial List/<init>(Ljava/util/ArrayList;)V";
        return commands;
    }

    @Override
    public String visit(NullValue nullValue) {
        String commands = "aconst_null";
        return commands;
    }

    @Override
    public String visit(IntValue intValue) {
        String commands = "";
        commands += "ldc " + intValue.getConstant();
        return commands;
    }

    @Override
    public String visit(BoolValue boolValue) {
        String commands = "";
        if (boolValue.getConstant())
            commands += "ldc 1";
        else
            commands += "ldc 0";
        return commands;
    }

    @Override
    public String visit(StringValue stringValue) {
        String commands = "";
        commands += "ldc \"" + stringValue.getConstant() + "\"";
        return commands;
    }

}