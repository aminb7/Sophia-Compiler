package main.visitor.typeChecker;

import main.ast.nodes.declaration.classDec.ClassDeclaration;
import main.ast.nodes.declaration.classDec.classMembersDec.ConstructorDeclaration;
import main.ast.nodes.declaration.classDec.classMembersDec.MethodDeclaration;
import main.ast.nodes.declaration.variableDec.VarDeclaration;
import main.ast.nodes.expression.*;
import main.ast.nodes.expression.values.ListValue;
import main.ast.nodes.expression.values.NullValue;
import main.ast.nodes.expression.values.primitive.BoolValue;
import main.ast.nodes.expression.values.primitive.IntValue;
import main.ast.nodes.expression.values.primitive.StringValue;

import main.ast.nodes.expression.operators.*;

import main.ast.types.NoType;
import main.ast.types.functionPointer.FptrType;
import main.symbolTable.exceptions.ItemNotFoundException;

import main.symbolTable.SymbolTable;
import main.symbolTable.items.*;

import main.ast.types.NullType;
import main.ast.types.Type;
import main.ast.types.list.ListNameType;
import main.ast.types.list.ListType;
import main.ast.types.single.*;

import main.compileErrorException.typeErrors.*;

import main.symbolTable.SymbolTable;
import main.symbolTable.utils.graph.Graph;
import main.visitor.Visitor;

import java.util.ArrayList;

public class ExpressionTypeChecker extends Visitor<Type> {
    private final Graph<String> classHierarchy;
    private ClassDeclaration currClassDeclaration;
    private MethodDeclaration currMethodDeclaration;

    boolean assignStmtIsLValue;
    boolean assignExprIsLValue;
    boolean unaryIsLValue;
    boolean isLiteral;

    boolean inMethodCallStmt;

    public ExpressionTypeChecker(Graph<String> classHierarchy) {
        this.classHierarchy = classHierarchy;
        this.assignStmtIsLValue = true;
        this.assignExprIsLValue = true;
        this.unaryIsLValue = true;
        this.isLiteral = false;
        this.inMethodCallStmt = false;
    }

    public void setCurrentClassDeclaration(ClassDeclaration currClassDeclaration){
        this.currClassDeclaration = currClassDeclaration;
    }

    public void setCurrentMethodDeclaration(MethodDeclaration currMethodDeclaration){
        this.currMethodDeclaration = currMethodDeclaration;
    }

    boolean firstIsSubTypeOfSecond(Type first, Type second){
        if (first instanceof NoType) {
            return true;
        }

        if (second instanceof NoType){
            return false;
        }

        if (first instanceof IntType){
            if (second instanceof IntType)
                return true;
        }

        if (first instanceof BoolType){
            if (second instanceof BoolType)
                return true;
        }

        if (first instanceof StringType){
            if (second instanceof StringType)
                return true;
        }

        if (first instanceof ClassType){
            if (second instanceof ClassType){
                return (classHierarchy.isSecondNodeAncestorOf(((ClassType) first).getClassName().getName(), ((ClassType) second).getClassName().getName()) ||
                        ((ClassType) first).getClassName().getName().equals(((ClassType) second).getClassName().getName()));
            }
        }

        if (first instanceof FptrType){
            if (second instanceof FptrType){
                if (((FptrType) first).getArgumentsTypes().size() == ((FptrType) second).getArgumentsTypes().size() &&
                        firstIsSubTypeOfSecond(((FptrType) first).getReturnType(), ((FptrType) second).getReturnType())){
                    for (int i = 0; i < ((FptrType) first).getArgumentsTypes().size(); i++){
                        if (!firstIsSubTypeOfSecond(((FptrType) first).getArgumentsTypes().get(i), ((FptrType) second).getArgumentsTypes().get(i))){
                            return false;
                        }
                    }
                    return true;
                }
            }
        }

        if (first instanceof ListType){
            if (second instanceof ListType && ((ListType) first).getElementsTypes().size() == ((ListType) second).getElementsTypes().size()){
                for (int i = 0; i < ((ListType) first).getElementsTypes().size(); i++){
                    if (!firstIsSubTypeOfSecond(((ListType) first).getElementsTypes().get(i).getType(), ((ListType) second).getElementsTypes().get(i).getType())){
                        return false;
                    }
                }
                return true;
            }
        }

        if (first instanceof NullType){
            if (second instanceof NullType || second instanceof ClassType || second instanceof FptrType){
                return true;
            }
        }

        return false;
    }

    @Override
    public Type visit(BinaryExpression binaryExpression) {
        BinaryOperator operator = binaryExpression.getBinaryOperator();

        if (operator == BinaryOperator.or || operator == BinaryOperator.and){
            Type type1 = binaryExpression.getFirstOperand().accept(this);
            Type type2 = binaryExpression.getSecondOperand().accept(this);
            assignStmtIsLValue = false;
            assignExprIsLValue = false;
            unaryIsLValue = false;

            if (type1 instanceof NoType && type2 instanceof NoType){
                return new NoType();
            }
            if (type1 instanceof NoType && type2 instanceof BoolType){
                return new NoType();
            }
            if (type1 instanceof BoolType && type2 instanceof NoType){
                return new BoolType();
            }
            if (type1 instanceof BoolType && type2 instanceof BoolType){
                return new BoolType();
            }
            UnsupportedOperandType exception = new UnsupportedOperandType(binaryExpression.getLine(), operator.toString());
            binaryExpression.addError(exception);
            return new NoType();
        }

        if (operator == BinaryOperator.add || operator == BinaryOperator.sub || operator == BinaryOperator.mult || operator == BinaryOperator.div || operator == BinaryOperator.mod){
            Type type1 = binaryExpression.getFirstOperand().accept(this);
            Type type2 = binaryExpression.getSecondOperand().accept(this);
            assignStmtIsLValue = false;
            assignExprIsLValue = false;
            unaryIsLValue = false;

            if (type1 instanceof NoType && type2 instanceof NoType){
                return new NoType();
            }
            if (type1 instanceof NoType && type2 instanceof IntType){
                return new NoType();
            }
            if (type1 instanceof IntType && type2 instanceof NoType){
                return new NoType();
            }
            if (type1 instanceof IntType && type2 instanceof IntType){
                return new IntType();
            }
            UnsupportedOperandType exception = new UnsupportedOperandType(binaryExpression.getLine(), operator.toString());
            binaryExpression.addError(exception);
            return new NoType();
        }

        if (operator == BinaryOperator.assign){
            assignExprIsLValue = true;
            Type type1 = binaryExpression.getFirstOperand().accept(this);

            if (!assignExprIsLValue){
                LeftSideNotLvalue exception = new LeftSideNotLvalue(binaryExpression.getFirstOperand().getLine());
                binaryExpression.addError(exception);
                binaryExpression.getSecondOperand().accept(this);
                unaryIsLValue = false;
                assignStmtIsLValue = false;
                return new NoType();
            }

            Type type2 = binaryExpression.getSecondOperand().accept(this);
            unaryIsLValue = false;
            assignStmtIsLValue = false;

            if (type1 instanceof NoType || type2 instanceof NoType){
                return new NoType();
            }
            if (firstIsSubTypeOfSecond(type2, type1)){
                return type2;
            }
            unaryIsLValue = false;
            assignStmtIsLValue = false;

            UnsupportedOperandType exception = new UnsupportedOperandType(binaryExpression.getLine(), operator.toString());
            binaryExpression.addError(exception);
            return new NoType();
        }

        if (operator == BinaryOperator.gt || operator == BinaryOperator.lt){
            Type type1 = binaryExpression.getFirstOperand().accept(this);
            Type type2 = binaryExpression.getSecondOperand().accept(this);
            assignStmtIsLValue = false;
            assignExprIsLValue = false;
            unaryIsLValue = false;

            if (type1 instanceof NoType && type2 instanceof NoType){
                return new NoType();
            }
            if (type1 instanceof NoType && type2 instanceof IntType){
                return new NoType();
            }
            if (type1 instanceof IntType && type2 instanceof NoType){
                return new NoType();
            }
            if (type1 instanceof IntType && type2 instanceof IntType){
                return new BoolType();
            }
            UnsupportedOperandType exception = new UnsupportedOperandType(binaryExpression.getLine(), operator.toString());
            binaryExpression.addError(exception);
            return new NoType();
        }

        if (operator == BinaryOperator.eq || operator == BinaryOperator.neq){
            Type type1 = binaryExpression.getFirstOperand().accept(this);
            Type type2 = binaryExpression.getSecondOperand().accept(this);
            assignStmtIsLValue = false;
            assignExprIsLValue = false;
            unaryIsLValue = false;

            if (type1 instanceof ListType || type2 instanceof ListType){
                UnsupportedOperandType exception = new UnsupportedOperandType(binaryExpression.getLine(), operator.toString());
                binaryExpression.addError(exception);
                return new NoType();
            }

            // ClassType
            if (type1 instanceof NullType && type2 instanceof NullType){
                return new BoolType();
            }

            if (type1 instanceof NullType && type2 instanceof ClassType){
                return new BoolType();
            }

            if (type1 instanceof ClassType && type2 instanceof NullType){
                return new BoolType();
            }

            if (type1 instanceof ClassType && type2 instanceof ClassType){
                if (firstIsSubTypeOfSecond(type1, type2) && firstIsSubTypeOfSecond(type2, type1))
                    return new BoolType();
                UnsupportedOperandType exception = new UnsupportedOperandType(binaryExpression.getLine(), operator.toString());
                binaryExpression.addError(exception);
                return new NoType();
            }

            // FptrType
            if (type1 instanceof NullType && type2 instanceof FptrType){
                return new BoolType();
            }

            if (type1 instanceof FptrType && type2 instanceof NullType){
                return new BoolType();
            }

            if (type1 instanceof FptrType && type2 instanceof FptrType){
                if (firstIsSubTypeOfSecond(type1, type2) && firstIsSubTypeOfSecond(type2, type1))
                    return new BoolType();
                UnsupportedOperandType exception = new UnsupportedOperandType(binaryExpression.getLine(), operator.toString());
                binaryExpression.addError(exception);
                return new NoType();
            }

            if (firstIsSubTypeOfSecond(type1, type2) && firstIsSubTypeOfSecond(type2, type1))
                return new BoolType();

            if (type1 instanceof NoType || type2 instanceof NoType)
                return new NoType();
            UnsupportedOperandType exception = new UnsupportedOperandType(binaryExpression.getLine(), operator.toString());
            binaryExpression.addError(exception);
            return new NoType();
        }

        return new NoType();
    }

    @Override
    public Type visit(UnaryExpression unaryExpression) {

        UnaryOperator operator = unaryExpression.getOperator();

        if (operator == UnaryOperator.not){
            Type type = unaryExpression.getOperand().accept(this);
            assignStmtIsLValue = false;
            assignExprIsLValue = false;
            unaryIsLValue = false;

            if (type instanceof NoType){
                return new NoType();
            }
            if (type instanceof BoolType){
                return new BoolType();
            }
            UnsupportedOperandType exception = new UnsupportedOperandType(unaryExpression.getLine(), operator.toString());
            unaryExpression.addError(exception);
            return new NoType();
        }

        if (operator == UnaryOperator.minus){
            Type type = unaryExpression.getOperand().accept(this);
            assignStmtIsLValue = false;
            assignExprIsLValue = false;
            unaryIsLValue = false;

            if (type instanceof NoType){
                return new NoType();
            }
            if (type instanceof IntType){
                return new IntType();
            }
            UnsupportedOperandType exception = new UnsupportedOperandType(unaryExpression.getLine(), operator.toString());
            unaryExpression.addError(exception);
            return new NoType();
        }

        if (operator == UnaryOperator.predec || operator == UnaryOperator.postdec || operator == UnaryOperator.preinc || operator == UnaryOperator.postinc){
            unaryIsLValue = true;
            Type type = unaryExpression.getOperand().accept(this);
            assignStmtIsLValue = false;
            assignExprIsLValue = false;
            if (!unaryIsLValue) {
                IncDecOperandNotLvalue exception = new IncDecOperandNotLvalue(unaryExpression.getOperand().getLine(), operator.toString());
                unaryExpression.addError(exception);
            }

            if (type instanceof NoType){
                return new NoType();
            }
            if ((type instanceof IntType) && unaryIsLValue){
                return new IntType();
            }
            if (type instanceof IntType)
                return new NoType();
            UnsupportedOperandType exception = new UnsupportedOperandType(unaryExpression.getLine(), operator.toString());
            unaryExpression.addError(exception);
            return new NoType();
        }

        return new NoType();
    }

    @Override
    public Type visit(ObjectOrListMemberAccess objectOrListMemberAccess) {
        Type objectType = objectOrListMemberAccess.getInstance().accept(this);

        assignStmtIsLValue = true;
        assignExprIsLValue = true;
        unaryIsLValue = true;
        if (objectType instanceof NoType)
            return new NoType();
        else if (objectType instanceof ClassType){
            try {
                String classKey = "Class_" + ((ClassType) objectType).getClassName().getName();
                ClassSymbolTableItem classSymbolTableItem = (ClassSymbolTableItem) SymbolTable.root.getItem(classKey, true);
                try{
                    String memberKey = "Field_" + objectOrListMemberAccess.getMemberName().getName();
                    FieldSymbolTableItem fieldSymbolTableItem = (FieldSymbolTableItem) classSymbolTableItem.getClassSymbolTable().getItem(memberKey, true);
                    assignStmtIsLValue = true;
                    assignExprIsLValue = true;
                    unaryIsLValue = true;
                    return fieldSymbolTableItem.getType();
                }
                catch (ItemNotFoundException e1) {
                    try{
                        String memberKey = "Method_" + objectOrListMemberAccess.getMemberName().getName();
                        MethodSymbolTableItem methodSymbolTableItem = (MethodSymbolTableItem) classSymbolTableItem.getClassSymbolTable().getItem(memberKey, true);
                        assignStmtIsLValue = false;
                        assignExprIsLValue = false;
                        unaryIsLValue = false;
                        return new FptrType(methodSymbolTableItem.getArgTypes(), methodSymbolTableItem.getReturnType());
                    }
                    catch (ItemNotFoundException e2) {
                        MemberNotAvailableInClass exception = new MemberNotAvailableInClass(objectOrListMemberAccess.getMemberName().getLine(),
                                objectOrListMemberAccess.getMemberName().getName(), ((ClassType) objectType).getClassName().getName());
                        objectOrListMemberAccess.addError(exception);
                        return new NoType();
                    }
                }
            }catch (ItemNotFoundException e) {
                ClassNotDeclared exception = new ClassNotDeclared(objectOrListMemberAccess.getLine(), ((ClassType) objectType).getClassName().getName());
                objectOrListMemberAccess.addError(exception);
                assignStmtIsLValue = true;
                assignExprIsLValue = true;
                unaryIsLValue = true;
                return new NoType();
            }
        }else if (objectType instanceof ListType){
            ArrayList<ListNameType> listTypes = ((ListType) objectType).getElementsTypes();
            for (ListNameType listNameType : listTypes){
                if (listNameType.getName().getName().equals(objectOrListMemberAccess.getMemberName().getName())
                        || listNameType.getType() instanceof NoType){
                    return listNameType.getType();
                }
            }

            ListMemberNotFound exception = new ListMemberNotFound(objectOrListMemberAccess.getMemberName().getLine(), objectOrListMemberAccess.getMemberName().getName());
            objectOrListMemberAccess.addError(exception);
            return new NoType();
        }
        else {
            assignStmtIsLValue = false;
            assignExprIsLValue = false;
            unaryIsLValue = false;
        }

        MemberAccessOnNoneObjOrListType exception = new MemberAccessOnNoneObjOrListType(objectOrListMemberAccess.getLine());
        objectOrListMemberAccess.addError(exception);

        return new NoType();
    }

    @Override
    public Type visit(Identifier identifier) {
        assignStmtIsLValue = true;
        assignExprIsLValue = true;
        unaryIsLValue = true;

        ArrayList<VarDeclaration> args = currMethodDeclaration.getArgs();
        for (VarDeclaration arg : args){
            if (arg.getVarName().getName().equals(identifier.getName())){
                return arg.getType();
            }
        }

        ArrayList<VarDeclaration> localVars = currMethodDeclaration.getLocalVars();
        for (VarDeclaration localVar : localVars){
            if (localVar.getVarName().getName().equals(identifier.getName())){
                return localVar.getType();
            }
        }

        VarNotDeclared exception = new VarNotDeclared(identifier.getLine(), identifier.getName());
        identifier.addError(exception);
        return new NoType();
    }

    @Override
    public Type visit(ListAccessByIndex listAccessByIndex) {
        boolean hasError = false;

        Type type1 = listAccessByIndex.getIndex().accept(this);


        if (!(type1 instanceof IntType) && !(type1 instanceof NoType)){
            ListIndexNotInt exception = new ListIndexNotInt(listAccessByIndex.getIndex().getLine());
            listAccessByIndex.addError(exception);
            hasError = true;
        }

        Type type2 = listAccessByIndex.getInstance().accept(this);

        if (!(type2 instanceof ListType) && !(type2 instanceof NoType)){
            ListAccessByIndexOnNoneList exception = new ListAccessByIndexOnNoneList(listAccessByIndex.getInstance().getLine());
            listAccessByIndex.addError(exception);
            hasError = true;
        }

        //if (type1 instanceof NoType) return new NoType(); // Check later: erroraye badi shayad az dast beran.
        if (type2 instanceof NoType) return new NoType();

        if (type2 instanceof ListType){
            boolean sameElements = true;
            if (((ListType) type2).getElementsTypes().size() > 0){
                Type firstType = ((ListType) type2).getElementsTypes().get(0).getType();
                for (int i = 1; i < ((ListType) type2).getElementsTypes().size(); i++){ // check later: a[3] (a is (IntType, IntType, NoType))
                    if (!(firstIsSubTypeOfSecond(firstType, ((ListType) type2).getElementsTypes().get(i).getType()) &&
                            firstIsSubTypeOfSecond(((ListType) type2).getElementsTypes().get(i).getType(), firstType)) &&
                            !(((ListType) type2).getElementsTypes().get(i).getType() instanceof NoType))
                        sameElements = false;
                }
            }
            if (sameElements){
                if (((ListType) type2).getElementsTypes().size() > 0) {
                    if (hasError)
                        return new NoType();
                    else {
                        return ((ListType) type2).getElementsTypes().get(0).getType();
                    }
                }
                else
                    return new NoType();
            }
            else{
                if (type1 instanceof NoType) {
                    CantUseExprAsIndexOfMultiTypeList exception = new CantUseExprAsIndexOfMultiTypeList(listAccessByIndex.getIndex().getLine());
                    listAccessByIndex.addError(exception);
                    return new NoType();
                }
                if (listAccessByIndex.getIndex() instanceof IntValue) {
                    if (((IntValue) listAccessByIndex.getIndex()).getConstant() >= ((ListType) type2).getElementsTypes().size()) {
                        if (hasError)
                            return new NoType();
                        else
                            return ((ListType) type2).getElementsTypes().get(0).getType();
                    } else {
                        if (hasError)
                            return new NoType();
                        else
                            return ((ListType) type2).getElementsTypes().get(((IntValue) listAccessByIndex.getIndex()).getConstant()).getType();
                    }

                }
                CantUseExprAsIndexOfMultiTypeList exception = new CantUseExprAsIndexOfMultiTypeList(listAccessByIndex.getIndex().getLine());
                listAccessByIndex.addError(exception);
                return new NoType();
            }
        }

        return new NoType();
    }

    @Override
    public Type visit(MethodCall methodCall) {
        Type type = methodCall.getInstance().accept(this);
        assignStmtIsLValue = false;
        assignExprIsLValue = false;
        unaryIsLValue = false;
        if (type instanceof NoType){
            ArrayList<Expression> args = methodCall.getArgs();
            for (int i = 0; i < args.size(); i++) {
                args.get(i).accept(this);
            }
            assignStmtIsLValue = false;
            assignExprIsLValue = false;
            unaryIsLValue = false;
            return new NoType();
        }
        if (!(type instanceof FptrType)){
            CallOnNoneFptrType exception = new CallOnNoneFptrType(methodCall.getLine());
            methodCall.addError(exception);
            return new NoType();
        }

        boolean hasError = false;

        if ((((FptrType) type).getReturnType() instanceof NullType) && !inMethodCallStmt){
            CantUseValueOfVoidMethod exception = new CantUseValueOfVoidMethod(methodCall.getLine());
            methodCall.addError(exception);
            hasError = true;
        }

        ArrayList<Expression> args = methodCall.getArgs();

        if (args.size() != ((FptrType) type).getArgumentsTypes().size()){
            MethodCallNotMatchDefinition exception = new MethodCallNotMatchDefinition(methodCall.getLine());
            methodCall.addError(exception);
            hasError = true;
        }

        for (int i = 0; i < args.size(); i++) {
            Type argType = args.get(i).accept(this);
            if (!hasError && !firstIsSubTypeOfSecond(argType, ((FptrType) type).getArgumentsTypes().get(i))){ // Check if later
                MethodCallNotMatchDefinition exception = new MethodCallNotMatchDefinition(methodCall.getLine());
                methodCall.addError(exception);
                hasError = true;
            }
        }

        assignStmtIsLValue = false;
        assignExprIsLValue = false;
        unaryIsLValue = false;

        if (hasError) return new NoType();
        return ((FptrType) type).getReturnType();
    }

    @Override
    public Type visit(NewClassInstance newClassInstance) {
        assignStmtIsLValue = false;
        assignExprIsLValue = false;
        unaryIsLValue = false;
        boolean hasError = false;
        ClassSymbolTableItem classSymbolTableItem = null;
        try {
            String classKey = "Class_" + newClassInstance.getClassType().getClassName().getName();
            classSymbolTableItem = (ClassSymbolTableItem) SymbolTable.root.getItem(classKey, true);
        }
        catch(ItemNotFoundException e){
            ClassNotDeclared exception = new ClassNotDeclared(newClassInstance.getLine(), newClassInstance.getClassType().getClassName().getName());
            newClassInstance.addError(exception);

            ArrayList<Expression> args = newClassInstance.getArgs();
            for (int i = 0; i < args.size(); i++) {
                Type argType = args.get(i).accept(this);
            }
            assignStmtIsLValue = false;
            assignExprIsLValue = false;
            unaryIsLValue = false;
            return new NoType();
        }

        ConstructorDeclaration constructorDeclaration = classSymbolTableItem.getClassDeclaration().getConstructor();

        ArrayList<Expression> args = newClassInstance.getArgs();

        if (constructorDeclaration != null){
            ArrayList<VarDeclaration> constructorArgs = constructorDeclaration.getArgs();

            if (args.size() != constructorArgs.size()){
                ConstructorArgsNotMatchDefinition exception = new ConstructorArgsNotMatchDefinition(newClassInstance);
                newClassInstance.addError(exception);
                hasError = true;
            }

            for (int i = 0; i < args.size(); i++) {
                Type argType = args.get(i).accept(this);
                if (!hasError && !firstIsSubTypeOfSecond(argType, constructorArgs.get(i).getType())){ // Check if later
                    ConstructorArgsNotMatchDefinition exception = new ConstructorArgsNotMatchDefinition(newClassInstance);
                    newClassInstance.addError(exception);
                    hasError = true;
                }
            }
            assignStmtIsLValue = false;
            assignExprIsLValue = false;
            unaryIsLValue = false;
        }
        else{
            for (int i = 0; i < args.size(); i++) {
                args.get(i).accept(this);
            }
            assignStmtIsLValue = false;
            assignExprIsLValue = false;
            unaryIsLValue = false;
            if (args.size() != 0){
                ConstructorArgsNotMatchDefinition exception = new ConstructorArgsNotMatchDefinition(newClassInstance);
                newClassInstance.addError(exception);
                hasError = true;
            }
        }


        if (hasError) return new NoType();
        return newClassInstance.getClassType();
    }

    @Override
    public Type visit(ThisClass thisClass) {
        assignStmtIsLValue = false;
        assignExprIsLValue = false;
        unaryIsLValue = false;
        return new ClassType(currClassDeclaration.getClassName());
    }

    @Override
    public Type visit(ListValue listValue) {
        ArrayList<Expression> elements = listValue.getElements();

        ListType listType = new ListType();
        for (Expression element : elements) {
            Type elementType = element.accept(this);
            listType.addElementType(new ListNameType(elementType));
        }

        assignStmtIsLValue = false;
        assignExprIsLValue = false;
        unaryIsLValue = false;
        return listType;
    }

    @Override
    public Type visit(NullValue nullValue) {
        assignStmtIsLValue = false;
        assignExprIsLValue = false;
        unaryIsLValue = false;
        return new NullType();
    }

    @Override
    public Type visit(IntValue intValue) {
        assignStmtIsLValue = false;
        assignExprIsLValue = false;
        unaryIsLValue = false;
        return new IntType();
    }

    @Override
    public Type visit(BoolValue boolValue) {
        assignStmtIsLValue = false;
        assignExprIsLValue = false;
        unaryIsLValue = false;
        return new BoolType();
    }

    @Override
    public Type visit(StringValue stringValue) {
        assignStmtIsLValue = false;
        assignExprIsLValue = false;
        unaryIsLValue = false;
        return new StringType();
    }
}