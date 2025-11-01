package com.beemediate.beemediate.infrastructure.odoo.config;

import static org.junit.Assert.assertEquals;

import java.util.Arrays;
import java.util.Collection;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

@RunWith(Parameterized.class)
public class OaFStatusParamTest {
	
    private final OdooApiConfig.OafStatus status;
    private final String expectedLabel;

    @Parameters
    public static Collection<Object[]> parameters() {
        return Arrays.asList(
                new Object []{ OdooApiConfig.OafStatus.NEW, "NEW" },
                new Object []{ OdooApiConfig.OafStatus.SHIPPED, "SHIPPED" },
                new Object []{ OdooApiConfig.OafStatus.CONFIRMED, "CONFIRMED" },
                new Object []{ OdooApiConfig.OafStatus.OPENTRANSERROR, "OPENTRANSERROR" },
                new Object []{ OdooApiConfig.OafStatus.CONTENTERROR, "CONTENTERROR" }
        );
    }

    public OaFStatusParamTest(OdooApiConfig.OafStatus status, String expectedLabel) {
        this.status = status;
        this.expectedLabel = expectedLabel;
    }

    @Test
    public void labelMatchesExpected() {
        assertEquals(expectedLabel, status.label);
    }
}