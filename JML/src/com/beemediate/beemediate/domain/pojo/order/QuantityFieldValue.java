package com.beemediate.beemediate.domain.pojo.order;

/***Specifica il "modo" con cui viene scritta la quantità nel OrderItem
 * <ul>
 * <li>FLOAT_WITH_COMMA: la quantità è con virgola mobile in formato "," (comma); </li>
 * <li>FLOAT_WITH_DOT: la quantità è con virgola mobile in formato "." (dot);</li>
 * <li>INTEGER: la quantità non ha virgola mobile;</li>
 * <li>NAN: la quantità non è scritta in forma numerica.</li>
 * </ul>*/
public enum QuantityFieldValue {
	FLOAT_WITH_COMMA, FLOAT_WITH_DOT, INTEGER, NAN;
}
